"""Module 4: Pocket Candidate Ranking.

Clusters under-covered (absent/partial) concepts into coherent pocket candidates
and ranks them by a composite score reflecting cluster size (with Mathlib novelty
weighting), infrastructure proximity, and concept coherence.

This module is purely algorithmic -- no LLM or API calls. It operates on the
outputs of Modules 1-3: VerificationReport, DensityReport, GapReport, the
original concepts dict, and all SearchResponse objects.

Three-step pipeline:
  1. Extract under-covered concepts from the VerificationReport.
  2. Cluster them by namespace prefix (with kind-based sub-clustering for
     large groups).
  3. Score each cluster and rank by composite score.

See docs/candidate_ranker/edge_finder_pocket_candidates.md for full design doc.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
from typing import Any

from edge_finder.analysis.density import DensityReport
from edge_finder.analysis.heuristics import GapReport
from edge_finder.search.models import SearchResponse
from edge_finder.verification import (
    ConceptKind,
    VerificationReport,
    VerificationStatus,
)

# ---------------------------------------------------------------------------
# Scoring weights (design doc Section 5, Step 3)
# ---------------------------------------------------------------------------

WEIGHT_CLUSTER_SIZE = 0.30
WEIGHT_INFRA_PROXIMITY = 0.35
WEIGHT_COHERENCE = 0.35

# Normalisation targets
MAX_EFFECTIVE_SIZE = 5  # effective_size at or above 5 scores 1.0
MAX_RELATED_VERIFIED = 3  # 3+ related verified concepts scores 1.0

# Partial concept novelty discount (design doc Section 5, Step 3a)
PARTIAL_WEIGHT = 0.5

# Minimum cluster size to be promoted to a candidate
MIN_CLUSTER_SIZE = 2

# Kind-based sub-clustering threshold (design doc Section 5, Step 2)
KIND_SPLIT_THRESHOLD = 5


# ---------------------------------------------------------------------------
# Data model (frozen dataclasses per project convention)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class UnderCoveredConcept:
    """A concept classified as absent or partial by the verification layer."""

    name: str
    kind: ConceptKind
    status: VerificationStatus  # ABSENT or PARTIAL only
    namespace_prefix: str


@dataclass(frozen=True)
class ConceptCluster:
    """An intermediate grouping of related under-covered concepts."""

    namespace_prefix: str
    concepts: list[UnderCoveredConcept]


@dataclass(frozen=True)
class ScoredCandidate:
    """A scored and ranked pocket candidate ready for output."""

    rank: int
    name: str
    concepts: list[str]
    concept_kinds: list[str]
    concept_statuses: list[str]
    related_verified: list[str]
    score: float
    score_breakdown: dict[str, float]
    justification: list[str]
    feasibility_notes: list[str]
    risk: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "rank": self.rank,
            "name": self.name,
            "concepts": self.concepts,
            "concept_kinds": self.concept_kinds,
            "concept_statuses": self.concept_statuses,
            "related_verified": self.related_verified,
            "score": round(self.score, 4),
            "score_breakdown": {
                k: round(v, 4) for k, v in self.score_breakdown.items()
            },
            "justification": self.justification,
            "feasibility_notes": self.feasibility_notes,
            "risk": self.risk,
        }


@dataclass(frozen=True)
class CandidateReport:
    """Top-level output of Module 4."""

    theme: str
    total_absent: int
    total_partial: int
    candidates: list[ScoredCandidate]
    unclustered_concepts: list[str]
    metadata: dict[str, object]

    def to_dict(self) -> dict[str, Any]:
        return {
            "theme": self.theme,
            "total_absent": self.total_absent,
            "total_partial": self.total_partial,
            "candidates": [c.to_dict() for c in self.candidates],
            "unclustered_concepts": self.unclustered_concepts,
            "metadata": self.metadata,
        }


# ---------------------------------------------------------------------------
# Step 1: Extract under-covered concepts
# ---------------------------------------------------------------------------


def _namespace_prefix(name: str) -> str:
    """Extract the top-level namespace prefix from a concept name.

    For dot-separated names (e.g., 'TropicalCurve.forward_image'), takes the
    first dot-segment and then applies PascalCase splitting. For non-dot names
    (e.g., 'TropicalVariety'), applies PascalCase splitting directly. This
    ensures that 'TropicalCurve' and 'TropicalCurve.forward_image' both map
    to 'Tropical'.

    For snake_case names without dots (e.g., 'tropical_sum'), uses the first
    underscore-separated segment as the prefix.
    """
    # Step 1: if dot-separated, take the first segment
    base = name.split(".")[0]

    # Step 2: PascalCase split — find first uppercase boundary after position 0
    # that produces a prefix of at least 3 characters.
    for i in range(1, len(base)):
        if base[i].isupper() and i >= 3:
            return base[:i]

    # Step 3: snake_case fallback — use first underscore segment if present
    if "_" in base:
        return base.split("_")[0]

    return base


def extract_under_covered(report: VerificationReport) -> list[UnderCoveredConcept]:
    """Extract concepts classified as absent or partial from a VerificationReport."""
    result = []
    for entry in report.entries:
        if entry.status in (VerificationStatus.ABSENT, VerificationStatus.PARTIAL):
            result.append(
                UnderCoveredConcept(
                    name=entry.concept,
                    kind=entry.kind,
                    status=entry.status,
                    namespace_prefix=_namespace_prefix(entry.concept),
                )
            )
    return result


# ---------------------------------------------------------------------------
# Step 2: Cluster concepts by namespace prefix
# ---------------------------------------------------------------------------


def cluster_concepts(
    concepts: list[UnderCoveredConcept],
) -> tuple[list[ConceptCluster], list[str]]:
    """Group under-covered concepts into clusters by namespace prefix.

    Returns (clusters, unclustered_concept_names). Clusters with fewer than
    MIN_CLUSTER_SIZE concepts are dissolved into the unclustered list. Large
    clusters (> KIND_SPLIT_THRESHOLD) are sub-split by ConceptKind.
    """
    # Group by namespace prefix (case-insensitive to merge PascalCase and
    # snake_case variants, e.g., 'Tropical' and 'tropical').
    groups: dict[str, list[UnderCoveredConcept]] = defaultdict(list)
    prefix_canonical: dict[str, str] = {}  # lowered -> first-seen casing
    for concept in concepts:
        key = concept.namespace_prefix.lower()
        if key not in prefix_canonical:
            prefix_canonical[key] = concept.namespace_prefix
        groups[key].append(concept)

    clusters: list[ConceptCluster] = []
    unclustered: list[str] = []

    for key, members in sorted(groups.items()):
        prefix = prefix_canonical[key]  # use original casing for display
        if len(members) < MIN_CLUSTER_SIZE:
            unclustered.extend(m.name for m in members)
            continue

        if len(members) > KIND_SPLIT_THRESHOLD:
            # Sub-split by kind: primitives form the core, others are separate
            by_kind: dict[ConceptKind, list[UnderCoveredConcept]] = defaultdict(list)
            for m in members:
                by_kind[m.kind].append(m)

            for kind, kind_members in by_kind.items():
                if len(kind_members) < MIN_CLUSTER_SIZE:
                    unclustered.extend(m.name for m in kind_members)
                else:
                    kind_label = kind.value.replace("_", " ")
                    if kind_label.endswith("y"):
                        suffix = kind_label[:-1] + "ies"
                    else:
                        suffix = kind_label + "s"
                    clusters.append(
                        ConceptCluster(
                            namespace_prefix=f"{prefix} ({suffix})",
                            concepts=kind_members,
                        )
                    )
        else:
            clusters.append(ConceptCluster(namespace_prefix=prefix, concepts=members))

    return clusters, unclustered


# ---------------------------------------------------------------------------
# Step 3: Score and rank
# ---------------------------------------------------------------------------


def _avg_pairwise_lcp(names: list[str]) -> float:
    """Average pairwise longest common prefix length among concept names."""
    if len(names) < 2:
        return 0.0
    total = 0
    count = 0
    for a, b in combinations(names, 2):
        lcp = 0
        for ca, cb in zip(a, b):
            if ca == cb:
                lcp += 1
            else:
                break
        total += lcp
        count += 1
    return total / count if count else 0.0


def _generate_name(prefix: str, concepts: list[UnderCoveredConcept]) -> str:
    """Generate a human-readable candidate name from the cluster prefix and kinds."""
    kinds = {c.kind for c in concepts}
    if len(kinds) == 1 and ConceptKind.PRIMITIVE in kinds:
        return f"{prefix} Core"
    elif ConceptKind.PRIMITIVE in kinds:
        return f"{prefix} Extensions"
    else:
        return f"{prefix} Utilities"


def _generate_justification(
    cluster: ConceptCluster,
    related_verified: list[str],
    absent_count: int,
    partial_count: int,
) -> list[str]:
    """Produce human-readable justification lines for a scored candidate."""
    lines: list[str] = []

    total = len(cluster.concepts)
    status_parts = []
    if absent_count > 0:
        status_parts.append(f"{absent_count} absent")
    if partial_count > 0:
        status_parts.append(f"{partial_count} partial")
    status_str = " and ".join(status_parts)

    kinds = {c.kind.value for c in cluster.concepts}
    kind_str = ", ".join(sorted(kinds))
    lines.append(
        f"{total} under-covered concepts ({status_str}) "
        f"of kind [{kind_str}] sharing the '{cluster.namespace_prefix}' prefix"
    )

    if related_verified:
        lines.append(
            f"Existing infrastructure: {len(related_verified)} verified "
            f"concept(s) in the same namespace"
        )
    else:
        lines.append("No verified concepts found in the same namespace")

    return lines


def _generate_feasibility_notes(
    related_verified: list[str],
    infra_score: float,
) -> list[str]:
    """Produce feasibility notes based on infrastructure proximity."""
    notes: list[str] = []
    if infra_score >= 0.67:
        notes.append(
            f"Strong infrastructure: {len(related_verified)} verified "
            f"declarations in the same namespace provide a solid foundation"
        )
    elif infra_score >= 0.33:
        notes.append(
            f"Moderate infrastructure: {len(related_verified)} verified "
            f"declaration(s) in the same namespace"
        )
    else:
        notes.append(
            "Weak infrastructure: few or no verified declarations in the "
            "same namespace; implementation may need to build from scratch"
        )
    return notes


def _assess_risk(gap_confidence: str, infra_score: float) -> str:
    """Determine risk level from gap confidence and infrastructure proximity."""
    if gap_confidence == "high" and infra_score < 0.3:
        return "high"
    elif gap_confidence == "high" and infra_score >= 0.3:
        return "moderate"
    elif gap_confidence in ("moderate", "low"):
        return "moderate"
    # Fallback for informational / insufficient_signal
    return "low"


def _extract_gap_confidence(gap_report: GapReport) -> str:
    """Extract the gap confidence tier from the GapReport."""
    for finding in gap_report.findings:
        if finding.category == "concept_coverage_gap":
            return finding.confidence
        if finding.category == "well_covered":
            return finding.confidence
    return "low"


def _extract_coverage_ratio(verification: VerificationReport) -> float:
    """Extract coverage ratio from the verification report."""
    return verification.coverage_ratio


def score_cluster(
    cluster: ConceptCluster,
    verified_names: list[str],
    gap_confidence: str,
) -> ScoredCandidate:
    """Score a single concept cluster and produce a ScoredCandidate (unranked).

    The rank field is set to 0 here; the caller assigns final ranks after
    sorting all candidates by score.
    """
    concepts = cluster.concepts

    # --- Cluster size score (with novelty weighting) ---
    absent_count = sum(1 for c in concepts if c.status == VerificationStatus.ABSENT)
    partial_count = sum(1 for c in concepts if c.status == VerificationStatus.PARTIAL)
    effective_size = absent_count + PARTIAL_WEIGHT * partial_count
    size_score = min(effective_size / MAX_EFFECTIVE_SIZE, 1.0)

    # --- Infrastructure proximity score ---
    cluster_prefix = cluster.namespace_prefix.split(" (")[0]  # strip kind suffix
    related = sorted(
        set(
            v
            for v in verified_names
            if _namespace_prefix(v).lower() == cluster_prefix.lower()
        )
    )
    infra_score = min(len(related) / MAX_RELATED_VERIFIED, 1.0)

    # --- Concept coherence score ---
    primitive_count = sum(1 for c in concepts if c.kind == ConceptKind.PRIMITIVE)
    primitive_ratio = primitive_count / len(concepts) if concepts else 0.0

    names = [c.name for c in concepts]
    avg_lcp = _avg_pairwise_lcp(names)
    avg_name_len = sum(len(n) for n in names) / len(names) if names else 1.0
    name_similarity = avg_lcp / avg_name_len if avg_name_len > 0 else 0.0
    # Clamp to [0, 1]
    name_similarity = min(name_similarity, 1.0)

    coherence_score = 0.5 * primitive_ratio + 0.5 * name_similarity

    # --- Composite score ---
    composite = (
        WEIGHT_CLUSTER_SIZE * size_score
        + WEIGHT_INFRA_PROXIMITY * infra_score
        + WEIGHT_COHERENCE * coherence_score
    )

    # --- Justification and risk ---
    justification = _generate_justification(
        cluster, related, absent_count, partial_count
    )
    feasibility_notes = _generate_feasibility_notes(related, infra_score)
    risk = _assess_risk(gap_confidence, infra_score)

    return ScoredCandidate(
        rank=0,  # assigned by caller after sorting
        name=_generate_name(cluster.namespace_prefix, concepts),
        concepts=[c.name for c in concepts],
        concept_kinds=[c.kind.value for c in concepts],
        concept_statuses=[c.status.value for c in concepts],
        related_verified=related,
        score=composite,
        score_breakdown={
            "cluster_size": WEIGHT_CLUSTER_SIZE * size_score,
            "infrastructure_proximity": WEIGHT_INFRA_PROXIMITY * infra_score,
            "concept_coherence": WEIGHT_COHERENCE * coherence_score,
        },
        justification=justification,
        feasibility_notes=feasibility_notes,
        risk=risk,
    )


# ---------------------------------------------------------------------------
# Top-level entry point
# ---------------------------------------------------------------------------


def rank_candidates(
    *,
    verification: VerificationReport,
    density: DensityReport,
    gap: GapReport,
    concepts: dict,
    responses: list[SearchResponse],
    theme: str,
) -> CandidateReport:
    """Produce a ranked CandidateReport from pipeline outputs.

    This is the main entry point for Module 4. It:
      1. Extracts under-covered concepts from the verification report.
      2. Clusters them by namespace prefix.
      3. Scores and ranks each cluster.
      4. Returns a CandidateReport ready for JSON serialization.
    """
    # Step 1: extract
    under_covered = extract_under_covered(verification)

    if not under_covered:
        return CandidateReport(
            theme=theme,
            total_absent=verification.absent_count,
            total_partial=verification.partial_count,
            candidates=[],
            unclustered_concepts=[],
            metadata={
                "gap_confidence": _extract_gap_confidence(gap),
                "coverage_ratio": _extract_coverage_ratio(verification),
                "scoring_version": "1.0",
            },
        )

    # Collect verified concept names for infrastructure proximity scoring.
    # Deduplicate: the verification report may contain duplicate entries for the
    # same concept (e.g., from re-mapping or targeted search producing two entries).
    verified_names = sorted(
        set(
            entry.concept
            for entry in verification.entries
            if entry.status == VerificationStatus.VERIFIED
        )
    )

    # Step 2: cluster
    clusters, unclustered = cluster_concepts(under_covered)

    # Step 3: score
    gap_confidence = _extract_gap_confidence(gap)
    scored = [
        score_cluster(cluster, verified_names, gap_confidence) for cluster in clusters
    ]

    # Sort by descending score, then assign ranks
    scored.sort(key=lambda c: c.score, reverse=True)
    ranked = []
    for i, candidate in enumerate(scored, start=1):
        # Frozen dataclass: reconstruct with rank assigned
        ranked.append(
            ScoredCandidate(
                rank=i,
                name=candidate.name,
                concepts=candidate.concepts,
                concept_kinds=candidate.concept_kinds,
                concept_statuses=candidate.concept_statuses,
                related_verified=candidate.related_verified,
                score=candidate.score,
                score_breakdown=candidate.score_breakdown,
                justification=candidate.justification,
                feasibility_notes=candidate.feasibility_notes,
                risk=candidate.risk,
            )
        )

    return CandidateReport(
        theme=theme,
        total_absent=verification.absent_count,
        total_partial=verification.partial_count,
        candidates=ranked,
        unclustered_concepts=unclustered,
        metadata={
            "gap_confidence": gap_confidence,
            "coverage_ratio": _extract_coverage_ratio(verification),
            "scoring_version": "1.0",
        },
    )
