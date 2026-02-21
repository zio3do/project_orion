"""Concept re-mapping: grounds LLM-generated concept names against actual Mathlib declarations.

Given the concepts produced by the Concept Generator and the search results from
LeanExplore, this module asks the LLM to map each concept name to the closest
matching Mathlib declaration name. This addresses the naming convention mismatch
where the LLM generates textbook-style names (e.g., "first_isomorphism_theorem")
but Mathlib uses qualified Lean 4 names (e.g., "QuotientGroup.quotientKerEquivRange").

The re-mapping step runs after theme-level search and before verification. It
turns the LLM from a name-guesser into a name-matcher, which is an easier task.

Added in Iteration 5 (concept name grounding).
"""

from __future__ import annotations

import json
from typing import Any

from edge_finder.llm.client import LlmClient
from edge_finder.prompts import build_concept_remap_prompt
from edge_finder.search.models import SearchResponse


def remap_concepts(
    concepts: dict[str, Any],
    responses: list[SearchResponse],
    *,
    model: str = "gpt-4o-mini",
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    """Re-map concept names to Mathlib declaration names using the LLM.

    Extracts all unique declaration names from search results, then asks the LLM
    to match each concept to the best Mathlib name (or null if genuinely absent).

    Args:
        concepts: The Concept Generator's output (with primitives, operators, etc.)
        responses: Theme-level SearchResponse objects from LeanExplore.
        model: OpenAI model name.

    Returns:
        A tuple of:
        - A copy of concepts with remapped names (nulls replaced with originals,
          so downstream consumers always see strings).
        - The mapping log: list of {"original", "remapped", "reason"} dicts for
          auditability.
    """
    # Collect unique declaration names from all search results.
    result_names: list[str] = []
    seen: set[str] = set()
    for response in responses:
        for result in response.results:
            if result.name not in seen:
                seen.add(result.name)
                result_names.append(result.name)

    if not result_names:
        # No search results to match against; return concepts unchanged.
        return concepts, []

    theme = concepts.get("theme", "")
    prompt = build_concept_remap_prompt(theme, concepts, result_names)
    client = LlmClient(model=model)
    raw = client.complete_json(prompt)
    remap_result = json.loads(raw)

    # Build the remapped concepts dict. Preserve all original keys (theme,
    # candidate_namespaces, search_queries) and only replace the three concept
    # lists.
    remapped = dict(concepts)

    for key in ("primitives", "operators", "identity_families"):
        original_list = concepts.get(key, [])
        remapped_list = remap_result.get(key, original_list)

        # Safety: if the LLM returned a different-length list, fall back to
        # originals for the mismatched portion. Also treat the string "null"
        # as None (LLMs sometimes emit "null" instead of JSON null).
        final: list[str] = []
        for i, original in enumerate(original_list):
            if i < len(remapped_list) and remapped_list[i] is not None:
                value = str(remapped_list[i])
                if value.lower() == "null":
                    final.append(str(original))
                else:
                    final.append(value)
            else:
                final.append(str(original))
        remapped[key] = final

    # Extract the mapping log for auditability.
    mapping_log: list[dict[str, str]] = remap_result.get("mapping", [])

    return remapped, mapping_log
