"""Module 3b: Gap Heuristics Classifier.

Classifies potential gaps using per-concept verification data. Density metrics
are reported as informational context but do not produce gap claims.

Gap categories:

  - concept_coverage_gap:  Verification shows significant absent/partial concepts.
                           This is the sole gap signal. Confidence is tiered by
                           coverage ratio, calibrated against 6 Mathlib themes
                           (3 known-strong, 3 known-sparse) in Iteration 4.
  - density_context:       Informational summary of density metrics (not a gap
                           claim). Always present when declarations exist.
  - insufficient_signal:   Fallback when no declarations found or no verification
                           data provided.

Design rationale (Iteration 4): Calibration against 6 themes showed that
density-derived heuristics (missing_operator_abstraction, namespace_fragmentation,
middle_layer_gap, missing_thematic_file) fired identically on all themes regardless
of actual Mathlib coverage, because LeanExplore returns a fixed-size result set per
query. Only verification coverage separates well-developed from underdeveloped areas.
Density metrics are preserved for human inspection but removed as gap signals.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from edge_finder.analysis.density import DensityReport
from edge_finder.search.models import SearchResponse
from edge_finder.verification import VerificationReport, VerificationStatus


@dataclass(frozen=True)
class GapFinding:
    category: str
    confidence: str
    evidence: list[str]


@dataclass(frozen=True)
class GapReport:
    findings: list[GapFinding]

    def to_dict(self) -> dict[str, object]:
        return {
            "findings": [
                {
                    "category": finding.category,
                    "confidence": finding.confidence,
                    "evidence": finding.evidence,
                }
                for finding in self.findings
            ]
        }


def _compute_search_coverage(responses: list[SearchResponse]) -> float:
    """Fraction of search queries that returned at least one result.

    A low search coverage indicates API failures or poorly targeted queries,
    which means absent concepts may be false negatives rather than true gaps.
    """
    if not responses:
        return 0.0
    non_empty = sum(1 for r in responses if len(r.results) > 0)
    return round(non_empty / len(responses), 4)


def _downgrade_confidence(confidence: str) -> str:
    """Reduce confidence by one tier due to low search coverage."""
    mapping = {"high": "moderate", "moderate": "low", "low": "low"}
    return mapping.get(confidence, confidence)


def classify_gaps(
    report: DensityReport,
    verification: Optional[VerificationReport] = None,
    responses: Optional[list[SearchResponse]] = None,
) -> GapReport:
    """Classify potential gaps from verification data and density context.

    Args:
        report: Aggregate structural metrics from search results.
        verification: Per-concept verification report. Required for gap detection.
                      When absent, only density_context and insufficient_signal
                      are produced.
        responses: All search responses (theme + targeted). Used to compute
                   search coverage for confidence adjustment. Optional.

    Returns:
        A GapReport with one or more GapFinding entries.
    """
    findings: list[GapFinding] = []

    if report.total_declarations == 0:
        return GapReport(
            findings=[
                GapFinding(
                    category="insufficient_signal",
                    confidence="low",
                    evidence=["No declarations found in search responses"],
                )
            ]
        )

    # --- Search coverage ---
    search_coverage = _compute_search_coverage(responses) if responses else None
    low_search_coverage = search_coverage is not None and search_coverage < 0.7

    # --- Verification-derived gap signal (sole gap claim) ---
    if verification is not None and verification.total_count > 0:
        absent_count = verification.absent_count
        partial_count = verification.partial_count
        total = verification.total_count
        coverage = verification.coverage_ratio
        under_covered = absent_count + partial_count

        # Determine base confidence from coverage ratio.
        # Thresholds calibrated from 6-theme empirical test (Iteration 4):
        #   coverage < 0.3  -> high   (tropical geo 0.0, comb. species 0.23)
        #   coverage < 0.5  -> moderate (matroid 0.31, group hom. 0.26)
        #   coverage < 0.7  -> low    (nat add 0.53, list ops 0.68)
        #   coverage >= 0.7 -> no gap finding (well-covered)
        if coverage < 0.7:
            if coverage < 0.3:
                base_confidence = "high"
            elif coverage < 0.5:
                base_confidence = "moderate"
            else:
                base_confidence = "low"

            # Downgrade if many queries failed (unreliable absence signal).
            confidence = (
                _downgrade_confidence(base_confidence)
                if low_search_coverage
                else base_confidence
            )

            absent_names = [
                e.concept
                for e in verification.entries
                if e.status == VerificationStatus.ABSENT
            ]
            partial_names = [
                e.concept
                for e in verification.entries
                if e.status == VerificationStatus.PARTIAL
            ]
            evidence_lines = [
                f"Coverage ratio: {coverage} ({under_covered}/{total} concepts under-covered)",
            ]
            if absent_names:
                evidence_lines.append(f"Absent concepts: {', '.join(absent_names)}")
            if partial_names:
                evidence_lines.append(f"Partial concepts: {', '.join(partial_names)}")
            if search_coverage is not None:
                evidence_lines.append(
                    f"Search coverage: {search_coverage} "
                    f"({'low - some absences may be false negatives' if low_search_coverage else 'adequate'})"
                )
            findings.append(
                GapFinding(
                    category="concept_coverage_gap",
                    confidence=confidence,
                    evidence=evidence_lines,
                )
            )

    # --- Density context (informational, not a gap claim) ---
    density_evidence = [
        f"{report.total_declarations} declarations across {len(report.modules)} modules",
        f"{report.unique_namespaces} unique namespaces (2-level)",
        f"Module spread ratio: {report.module_spread_ratio}",
        f"Operator hit ratio: {report.operator_hit_ratio} ({len(report.operator_hits)} operators detected)",
    ]
    if search_coverage is not None:
        density_evidence.append(f"Search query coverage: {search_coverage}")
    findings.append(
        GapFinding(
            category="density_context",
            confidence="informational",
            evidence=density_evidence,
        )
    )

    # --- Fallback ---
    # If no verification data was provided (backward compat), the only finding
    # is density_context. Add insufficient_signal to flag that gap detection
    # could not run.
    has_gap_finding = any(f.category == "concept_coverage_gap" for f in findings)
    if verification is None:
        findings.append(
            GapFinding(
                category="insufficient_signal",
                confidence="low",
                evidence=[
                    "No verification data provided; gap detection requires verification"
                ],
            )
        )
    elif not has_gap_finding and verification.total_count > 0:
        # Coverage >= 0.7: no gap detected, report as well-covered.
        findings.append(
            GapFinding(
                category="well_covered",
                confidence="moderate",
                evidence=[
                    f"Coverage ratio: {verification.coverage_ratio} "
                    f"({verification.verified_count} verified, "
                    f"{verification.partial_count} partial out of "
                    f"{verification.total_count} concepts)",
                ],
            )
        )

    return GapReport(findings=findings)
