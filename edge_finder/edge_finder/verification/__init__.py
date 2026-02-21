"""Module 2: Per-Concept Verification Layer.

Given the concepts produced by the Concept Generator (Module 1) and the search
results from LeanExplore, this module classifies each hypothesized concept as:

  - verified:       An exact or near-exact match exists in Mathlib.
  - partial:        Related results exist but not the specific abstraction.
  - absent:         Searched and found nothing relevant.
  - name_mismatch:  The concept appears to exist under a different name.

Two-pass verification (Iteration 1 + 2):

  Pass 1 (verify_concepts): Matches concepts against the broad theme-level search
  results using name-based heuristics. Fast, no additional API calls.

  Pass 2 (refine_verification): For each concept classified as absent or partial,
  generates targeted search queries (e.g., the concept name itself, prefixed with
  candidate namespaces) and searches LeanExplore. Re-classifies the concept using
  the combined original + targeted results. This reduces false absences.

The key artifact is the VerificationReport, which provides a per-concept map of
status + evidence. This closes the concept-to-evidence disconnect identified in
the architecture doc (section 4).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Optional

from edge_finder.search.models import SearchResponse, SearchResult


class VerificationStatus(Enum):
    """Classification of a concept's presence in Mathlib."""

    VERIFIED = "verified"
    PARTIAL = "partial"
    ABSENT = "absent"
    NAME_MISMATCH = "name_mismatch"


class ConceptKind(Enum):
    """Which section of the concepts JSON a concept came from."""

    PRIMITIVE = "primitive"
    OPERATOR = "operator"
    IDENTITY_FAMILY = "identity_family"


@dataclass(frozen=True)
class MatchEvidence:
    """A single piece of evidence linking a concept to a search result."""

    result_name: str
    result_module: str
    match_type: str  # "exact", "qualified_suffix", "substring", "informalization"
    detail: str  # Human-readable explanation of why this counts as a match


@dataclass(frozen=True)
class VerificationEntry:
    """Verification result for a single concept."""

    concept: str
    kind: ConceptKind
    status: VerificationStatus
    matches: list[MatchEvidence]
    searched_queries: list[str]

    def to_dict(self) -> dict[str, Any]:
        return {
            "concept": self.concept,
            "kind": self.kind.value,
            "status": self.status.value,
            "matches": [
                {
                    "result_name": m.result_name,
                    "result_module": m.result_module,
                    "match_type": m.match_type,
                    "detail": m.detail,
                }
                for m in self.matches
            ],
            "searched_queries": self.searched_queries,
        }


@dataclass(frozen=True)
class VerificationReport:
    """Per-concept verification results for an entire concepts JSON."""

    entries: list[VerificationEntry]

    @property
    def verified_count(self) -> int:
        return sum(1 for e in self.entries if e.status == VerificationStatus.VERIFIED)

    @property
    def partial_count(self) -> int:
        return sum(1 for e in self.entries if e.status == VerificationStatus.PARTIAL)

    @property
    def absent_count(self) -> int:
        return sum(1 for e in self.entries if e.status == VerificationStatus.ABSENT)

    @property
    def name_mismatch_count(self) -> int:
        return sum(
            1 for e in self.entries if e.status == VerificationStatus.NAME_MISMATCH
        )

    @property
    def total_count(self) -> int:
        return len(self.entries)

    @property
    def coverage_ratio(self) -> float:
        """Fraction of concepts that are verified or partial."""
        if not self.entries:
            return 0.0
        found = sum(
            1
            for e in self.entries
            if e.status in (VerificationStatus.VERIFIED, VerificationStatus.PARTIAL)
        )
        return round(found / len(self.entries), 4)

    def to_dict(self) -> dict[str, Any]:
        return {
            "summary": {
                "total": self.total_count,
                "verified": self.verified_count,
                "partial": self.partial_count,
                "absent": self.absent_count,
                "name_mismatch": self.name_mismatch_count,
                "coverage_ratio": self.coverage_ratio,
            },
            "entries": [entry.to_dict() for entry in self.entries],
        }


# ---------------------------------------------------------------------------
# Concept extraction
# ---------------------------------------------------------------------------


def extract_concepts(concepts: dict[str, Any]) -> list[tuple[str, ConceptKind]]:
    """Pull verifiable concepts from the Concept Generator's output.

    Extracts items from 'primitives', 'operators', and 'identity_families'.
    Skips 'candidate_namespaces' and 'search_queries' (metadata, not claims).
    """
    items: list[tuple[str, ConceptKind]] = []
    for name in concepts.get("primitives", []):
        items.append((str(name), ConceptKind.PRIMITIVE))
    for name in concepts.get("operators", []):
        items.append((str(name), ConceptKind.OPERATOR))
    for name in concepts.get("identity_families", []):
        items.append((str(name), ConceptKind.IDENTITY_FAMILY))
    return items


# ---------------------------------------------------------------------------
# Matching heuristics
# ---------------------------------------------------------------------------


def _normalize(name: str) -> str:
    """Lowercase and strip whitespace for comparison."""
    return name.strip().lower()


def _find_matches(
    concept: str,
    results: list[SearchResult],
) -> list[MatchEvidence]:
    """Find all search results that match a concept, ranked by match quality.

    Match types (strongest to weakest):
      - exact:            result.name == concept (case-insensitive)
      - qualified_suffix: result.name ends with .concept (e.g., Finset.sum matches sum)
      - substring:        concept appears in result.name
      - informalization:  concept appears in result.informalization or docstring
                          but NOT in result.name (potential name_mismatch signal)
    """
    matches: list[MatchEvidence] = []
    norm_concept = _normalize(concept)

    for result in results:
        norm_name = _normalize(result.name)

        # Exact match
        if norm_name == norm_concept:
            matches.append(
                MatchEvidence(
                    result_name=result.name,
                    result_module=result.module,
                    match_type="exact",
                    detail=f"Exact name match: {result.name}",
                )
            )
            continue

        # Qualified suffix: result.name ends with ".concept"
        if norm_name.endswith("." + norm_concept):
            matches.append(
                MatchEvidence(
                    result_name=result.name,
                    result_module=result.module,
                    match_type="qualified_suffix",
                    detail=f"{result.name} ends with .{concept}",
                )
            )
            continue

        # Substring in name
        if norm_concept in norm_name:
            matches.append(
                MatchEvidence(
                    result_name=result.name,
                    result_module=result.module,
                    match_type="substring",
                    detail=f"'{concept}' found in name '{result.name}'",
                )
            )
            continue

        # Informalization / docstring match (but not in name -> name_mismatch signal)
        text_fields = " ".join(
            filter(None, [result.informalization, result.docstring])
        ).lower()
        if norm_concept in text_fields:
            matches.append(
                MatchEvidence(
                    result_name=result.name,
                    result_module=result.module,
                    match_type="informalization",
                    detail=f"'{concept}' found in docs/informalization of {result.name}, not in name",
                )
            )

    return matches


def _classify_status(matches: list[MatchEvidence]) -> VerificationStatus:
    """Determine verification status from match evidence.

    Rules:
      - Any exact or qualified_suffix match -> verified
      - Only substring matches -> partial (related but not the specific thing)
      - Only informalization matches -> name_mismatch (concept exists under different name)
      - No matches -> absent
    """
    if not matches:
        return VerificationStatus.ABSENT

    match_types = {m.match_type for m in matches}

    if "exact" in match_types or "qualified_suffix" in match_types:
        return VerificationStatus.VERIFIED
    if "substring" in match_types:
        return VerificationStatus.PARTIAL
    if "informalization" in match_types:
        return VerificationStatus.NAME_MISMATCH

    return VerificationStatus.ABSENT


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def verify_concepts(
    concepts: dict[str, Any],
    responses: list[SearchResponse],
) -> VerificationReport:
    """Verify each concept against collected search results.

    For each primitive, operator, and identity family in the concepts dict,
    searches all results from all responses for name-based matches, then
    classifies the concept as verified/partial/absent/name_mismatch.

    Args:
        concepts: The Concept Generator's output (with primitives, operators, etc.)
        responses: The list of SearchResponse objects from LeanExplore.

    Returns:
        A VerificationReport with one entry per concept.
    """
    # Flatten all results across all queries for matching.
    all_results: list[SearchResult] = []
    for response in responses:
        all_results.extend(response.results)

    # Deduplicate by declaration_id to avoid double-counting.
    seen_ids: set[int] = set()
    unique_results: list[SearchResult] = []
    for result in all_results:
        if result.declaration_id not in seen_ids:
            seen_ids.add(result.declaration_id)
            unique_results.append(result)

    # Collect query strings for the report.
    searched_queries = [r.query for r in responses]

    # Verify each concept.
    concept_items = extract_concepts(concepts)
    entries: list[VerificationEntry] = []

    for concept_name, concept_kind in concept_items:
        matches = _find_matches(concept_name, unique_results)
        status = _classify_status(matches)
        entries.append(
            VerificationEntry(
                concept=concept_name,
                kind=concept_kind,
                status=status,
                matches=matches,
                searched_queries=searched_queries,
            )
        )

    return VerificationReport(entries=entries)


# ---------------------------------------------------------------------------
# Iteration 2: Targeted query generation and refinement
# ---------------------------------------------------------------------------


def generate_targeted_queries(
    concept: str,
    candidate_namespaces: list[str],
) -> list[str]:
    """Generate targeted LeanExplore queries for a single concept.

    Strategy: produce a small set of queries likely to surface the concept if it
    exists in Mathlib. No LLM call — this is deterministic string manipulation.

    Query types:
      1. The concept name itself (e.g., "sum_add_distrib").
      2. For unqualified concepts (no dots): the concept prefixed with each
         top-level candidate namespace (e.g., "Finset.sum_add_distrib").
         Skips sub-namespaces to avoid nonsensical combinations.
      3. If the concept contains underscores, a space-separated version
         (e.g., "sum add distrib") for semantic search.

    Deduplicates and returns 1-5 queries typically.
    """
    queries: list[str] = []
    seen: set[str] = set()

    def _add(q: str) -> None:
        normalized = q.strip()
        if normalized and normalized.lower() not in seen:
            seen.add(normalized.lower())
            queries.append(normalized)

    # 1. Bare concept name.
    _add(concept)

    # 2. Namespace-prefixed variants (only for unqualified concepts).
    is_qualified = "." in concept
    if not is_qualified:
        # Use only top-level namespaces (no dots) to avoid nonsense like
        # "Finset.sum.sum_add_distrib". If the concept is "sum_add_distrib"
        # and namespaces are ["Finset", "Finset.sum", "BigOperators"],
        # we only try "Finset.sum_add_distrib" and "BigOperators.sum_add_distrib".
        top_level_ns = [ns for ns in candidate_namespaces if "." not in ns]
        for ns in top_level_ns:
            # Skip self-prefixing (e.g., don't generate "BigOperators.BigOperators").
            if ns.lower() != concept.lower():
                _add(f"{ns}.{concept}")

    # 3. Space-separated variant (for semantic search).
    if "_" in concept:
        spaced = concept.replace("_", " ")
        _add(spaced)

    return queries


async def refine_verification(
    initial_report: VerificationReport,
    concepts: dict[str, Any],
    search_fn: Callable[[str], Any],
) -> tuple[VerificationReport, list[SearchResponse]]:
    """Refine verification by running targeted searches for under-covered concepts.

    For each concept classified as absent or partial in the initial report,
    generates targeted queries, searches via search_fn, and re-classifies using
    the combined original + new results.

    Args:
        initial_report: The VerificationReport from verify_concepts() (pass 1).
        concepts: The Concept Generator's output (for candidate_namespaces).
        search_fn: An async callable that takes a query string and returns a
                   SearchResponse. Typically a partial of search_single().

    Returns:
        A tuple of (refined VerificationReport, list of new SearchResponses).
        The new responses should be logged by the caller.
    """
    candidate_namespaces = concepts.get("candidate_namespaces", [])
    new_responses: list[SearchResponse] = []
    refined_entries: list[VerificationEntry] = []

    for entry in initial_report.entries:
        # Only refine absent and partial concepts.
        if entry.status not in (VerificationStatus.ABSENT, VerificationStatus.PARTIAL):
            refined_entries.append(entry)
            continue

        # Generate and run targeted queries.
        targeted_queries = generate_targeted_queries(
            entry.concept, candidate_namespaces
        )
        if not targeted_queries:
            refined_entries.append(entry)
            continue

        # Search each targeted query.
        targeted_results: list[SearchResult] = []
        actual_queries: list[str] = list(entry.searched_queries)  # copy originals

        for query in targeted_queries:
            response: SearchResponse = await search_fn(query)
            new_responses.append(response)
            targeted_results.extend(response.results)
            actual_queries.append(query)

        # Deduplicate targeted results.
        seen_ids: set[int] = set()
        unique_targeted: list[SearchResult] = []
        for result in targeted_results:
            if result.declaration_id not in seen_ids:
                seen_ids.add(result.declaration_id)
                unique_targeted.append(result)

        # Re-match: combine original matches with new matches from targeted results.
        new_matches = _find_matches(entry.concept, unique_targeted)

        # Merge: keep original matches, add any new ones (deduplicate by result_name).
        existing_names = {m.result_name for m in entry.matches}
        combined_matches = list(entry.matches)
        for m in new_matches:
            if m.result_name not in existing_names:
                combined_matches.append(m)
                existing_names.add(m.result_name)

        # Re-classify with combined evidence.
        new_status = _classify_status(combined_matches)

        refined_entries.append(
            VerificationEntry(
                concept=entry.concept,
                kind=entry.kind,
                status=new_status,
                matches=combined_matches,
                searched_queries=actual_queries,
            )
        )

    return VerificationReport(entries=refined_entries), new_responses
