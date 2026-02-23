"""Concept re-mapping: grounds LLM-generated concept names against actual Mathlib declarations.

Given the concepts produced by the Concept Generator and the search results from
LeanExplore, this module asks the LLM to map each concept name to the closest
matching Mathlib declaration name. This addresses the naming convention mismatch
where the LLM generates textbook-style names (e.g., "first_isomorphism_theorem")
but Mathlib uses qualified Lean 4 names (e.g., "QuotientGroup.quotientKerEquivRange").

The re-mapping step runs after theme-level search and before verification. It
turns the LLM from a name-guesser into a name-matcher, which is an easier task.

Added in Iteration 5 (concept name grounding).
Updated in Iteration 7: added hallucination gate that rejects remaps to names
not present in the search results.
"""

from __future__ import annotations

import json
from typing import Any

from edge_finder.llm.client import LlmClient
from edge_finder.prompts import build_concept_remap_prompt
from edge_finder.search.models import SearchResponse


def _is_name_in_results(name: str, result_names_set: set[str]) -> bool:
    """Check if a remapped name is grounded in the search results.

    A name is grounded if:
    1. It appears exactly in the search results, OR
    2. It is a prefix of some result name (e.g., "fwdDiff" is a prefix of
       "fwdDiff_finset_sum"), OR
    3. Some result name starts with name + "_" or name + "." (namespace match).

    This prevents the LLM from hallucinating names that look plausible but
    don't correspond to any actual Mathlib declaration we found.
    """
    if name in result_names_set:
        return True
    # Check prefix/namespace matches.
    for result_name in result_names_set:
        if result_name.startswith(name + ".") or result_name.startswith(name + "_"):
            return True
        # Also check if the name appears as a qualified suffix
        # (e.g., "intervalIntegral" in "MeasureTheory.intervalIntegral").
        if result_name.endswith("." + name):
            return True
    return False


def remap_concepts(
    concepts: dict[str, Any],
    responses: list[SearchResponse],
    *,
    model: str = "gpt-4o-mini",
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    """Re-map concept names to Mathlib declaration names using the LLM.

    Extracts all unique declaration names from search results, then asks the LLM
    to match each concept to the best Mathlib name (or null if genuinely absent).

    Includes a hallucination gate (Iteration 7): any remapped name that does not
    appear in the search results is rejected and replaced with null + the original
    concept name. This prevents the LLM from confidently mapping to unrelated
    declarations.

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

    result_names_set = set(result_names)

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
                elif value == str(original):
                    # Kept as-is by the LLM (identity mapping). Accept.
                    final.append(value)
                elif _is_name_in_results(value, result_names_set):
                    # Remapped to a name that exists in search results. Accept.
                    final.append(value)
                else:
                    # HALLUCINATION GATE: LLM returned a name not in search
                    # results. Reject and keep the original.
                    final.append(str(original))
            else:
                final.append(str(original))
        remapped[key] = final

    # Extract the mapping log for auditability and apply hallucination gate.
    raw_mapping_log: list[dict[str, str]] = remap_result.get("mapping", [])
    mapping_log: list[dict[str, str]] = []
    for entry in raw_mapping_log:
        original = entry.get("original", "")
        remapped_name = entry.get("remapped")
        reason = entry.get("reason", "")

        if remapped_name and str(remapped_name).lower() != "null":
            remapped_str = str(remapped_name)
            if remapped_str == original:
                # Identity mapping, accept.
                mapping_log.append(entry)
            elif _is_name_in_results(remapped_str, result_names_set):
                # Valid remap, accept.
                mapping_log.append(entry)
            else:
                # Hallucinated name — reject and log.
                mapping_log.append(
                    {
                        "original": original,
                        "remapped": "null",
                        "reason": f"REJECTED (not in search results): {remapped_str}. Original reason: {reason}",
                    }
                )
        else:
            mapping_log.append(entry)

    return remapped, mapping_log
