"""Concept rewriter: propagates sibling evidence to stranded concepts.

After the concept remapper runs, some concepts are successfully matched to Mathlib
declarations (e.g., DiscreteDiff → fwdDiff) while others remain unmatched because
the remapper could not find a direct correspondence. This module identifies
"stranded" concepts — those the remapper left unchanged — that have successfully-
remapped siblings sharing the same mathematical domain. It then asks the LLM to
rewrite those stranded concepts using the sibling's actual Mathlib namespace as
evidence.

This addresses the systematic false-absence inflation where the concept generator
proposes textbook-style type hierarchies (DiscreteDerivative, DiscreteIntegral)
but Mathlib uses flat concrete functions (fwdDiff) with lemma-name prefixes.

Added in Iteration 6 (sibling-evidence propagation).
"""

from __future__ import annotations

import json
import re
from typing import Any

from edge_finder.llm.client import LlmClient
from edge_finder.prompts import build_concept_rewrite_prompt
from edge_finder.search.models import SearchResponse


def _pascal_stem(name: str) -> str:
    """Extract the first PascalCase word as the concept's stem.

    Examples:
        DiscreteDerivative   → Discrete
        DiscreteDerivative.chain → Discrete
        FiniteSum.summation  → Finite
        Nat.factorial        → Nat
        fwdDiff              → fwdDiff  (no PascalCase split)
    """
    # Strip any dot-qualified suffix first (e.g., "Foo.bar" → "Foo").
    base = name.split(".")[0]
    # Split on PascalCase boundaries.
    parts = re.findall(r"[A-Z][a-z0-9]*|[a-z][a-z0-9]*", base)
    if parts:
        return parts[0]
    return base


def _build_successful_remaps(remap_log: list[dict[str, str]]) -> dict[str, str]:
    """Build a mapping of original → remapped for successfully remapped concepts.

    Only includes entries where the remapper found a real Mathlib match
    (i.e., remapped is not null/None and differs from the original).
    """
    remaps: dict[str, str] = {}
    for entry in remap_log:
        original = entry.get("original", "")
        remapped = entry.get("remapped")
        if remapped and remapped != "null" and remapped != original and original:
            remaps[original] = remapped
    return remaps


def _find_sibling(
    concept: str,
    successful_remaps: dict[str, str],
    result_modules: dict[str, str],
) -> dict[str, str] | None:
    """Find the closest successfully-remapped sibling for a stranded concept.

    A sibling is a concept that shares the same PascalCase stem and was
    successfully remapped to a Mathlib declaration.

    Returns a dict with sibling_original, sibling_remapped, sibling_module
    or None if no sibling found.
    """
    concept_stem = _pascal_stem(concept)

    best_sibling = None
    best_score = -1

    for orig, remapped in successful_remaps.items():
        orig_stem = _pascal_stem(orig)
        if orig_stem.lower() == concept_stem.lower():
            # Prefer siblings whose original name shares more characters.
            common_len = len(_common_prefix(concept.lower(), orig.lower()))
            if common_len > best_score:
                best_score = common_len
                best_sibling = {
                    "sibling_original": orig,
                    "sibling_remapped": remapped,
                    "sibling_module": result_modules.get(remapped, ""),
                }

    return best_sibling


def _common_prefix(a: str, b: str) -> str:
    """Return the common prefix of two strings."""
    prefix = []
    for ca, cb in zip(a, b):
        if ca == cb:
            prefix.append(ca)
        else:
            break
    return "".join(prefix)


def _build_result_modules(responses: list[SearchResponse]) -> dict[str, str]:
    """Build a mapping of declaration name → module from search results."""
    modules: dict[str, str] = {}
    for response in responses:
        for result in response.results:
            if result.name not in modules:
                modules[result.name] = result.module or ""
    return modules


def _identify_stranded_concepts(
    concepts: dict[str, Any],
    remap_log: list[dict[str, str]],
) -> list[tuple[str, str, int]]:
    """Identify concepts that the remapper left unchanged.

    A concept is stranded if the remap_log shows it was mapped to null
    (meaning it kept its original generated name).

    Returns: list of (concept_name, kind, index_in_kind_list) tuples.
    """
    # Build the set of originals that were NOT successfully remapped.
    null_originals: set[str] = set()
    for entry in remap_log:
        original = entry.get("original", "")
        remapped = entry.get("remapped")
        if not remapped or remapped == "null":
            null_originals.add(original)

    stranded: list[tuple[str, str, int]] = []
    for kind in ("primitives", "operators", "identity_families"):
        kind_label = kind.rstrip("s")  # "primitive", "operator", "identity_family"
        if kind == "identity_families":
            kind_label = "identity_family"
        for i, concept in enumerate(concepts.get(kind, [])):
            if concept in null_originals:
                stranded.append((concept, kind_label, i))

    return stranded


def rewrite_concepts(
    concepts: dict[str, Any],
    remap_log: list[dict[str, str]],
    responses: list[SearchResponse],
    *,
    model: str = "gpt-4o-mini",
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    """Rewrite stranded concepts using sibling evidence.

    For each concept that the remapper left unchanged (null), this function
    checks whether a sibling concept (sharing the same PascalCase stem) was
    successfully remapped. If so, it sends the stranded concept + sibling
    evidence to the LLM and asks it to guess the Mathlib name.

    Args:
        concepts: The remapped concepts dict (output of remap_concepts).
        remap_log: The remap log from remap_concepts.
        responses: Theme-level SearchResponse objects from LeanExplore.
        model: OpenAI model name.

    Returns:
        A tuple of:
        - A copy of concepts with rewritten names (nulls stay as originals).
        - The rewrite log: list of dicts for auditability.
    """
    successful_remaps = _build_successful_remaps(remap_log)
    if not successful_remaps:
        # No successful remaps = no sibling evidence. Nothing to do.
        return concepts, []

    result_modules = _build_result_modules(responses)
    stranded = _identify_stranded_concepts(concepts, remap_log)

    if not stranded:
        # Everything was already remapped. Nothing to do.
        return concepts, []

    # Build the stranded concepts payload for the LLM.
    stranded_with_siblings: list[dict[str, str]] = []
    stranded_without_siblings: list[tuple[str, str, int]] = []

    for concept_name, kind, idx in stranded:
        sibling = _find_sibling(concept_name, successful_remaps, result_modules)
        if sibling:
            stranded_with_siblings.append(
                {
                    "concept": concept_name,
                    "kind": kind,
                    "sibling_original": sibling["sibling_original"],
                    "sibling_remapped": sibling["sibling_remapped"],
                    "sibling_module": sibling["sibling_module"],
                }
            )
        else:
            stranded_without_siblings.append((concept_name, kind, idx))

    if not stranded_with_siblings:
        # All stranded concepts lack siblings. Can't rewrite without evidence.
        return concepts, []

    # Collect result names for the prompt (same as remapper).
    result_names: list[str] = []
    seen: set[str] = set()
    for response in responses:
        for result in response.results:
            if result.name not in seen:
                seen.add(result.name)
                result_names.append(result.name)

    theme = concepts.get("theme", "")
    prompt = build_concept_rewrite_prompt(theme, stranded_with_siblings, result_names)
    client = LlmClient(model=model)
    raw = client.complete_json(prompt)
    rewrite_result = json.loads(raw)

    rewrites = rewrite_result.get("rewrites", [])

    # Apply rewrites to the concepts dict.
    rewritten = dict(concepts)
    rewrite_log: list[dict[str, str]] = []

    # Build a lookup: concept_name → rewritten_name from LLM response.
    rewrite_map: dict[str, str | None] = {}
    for i, entry in enumerate(stranded_with_siblings):
        concept_name = entry["concept"]
        if i < len(rewrites):
            rw = rewrites[i]
            rewritten_name = rw.get("rewritten")
            reason = rw.get("reason", "")
            # Treat the string "null" as None.
            if rewritten_name and str(rewritten_name).lower() != "null":
                rewrite_map[concept_name] = str(rewritten_name)
                rewrite_log.append(
                    {
                        "original": concept_name,
                        "rewritten": str(rewritten_name),
                        "sibling_original": entry["sibling_original"],
                        "sibling_remapped": entry["sibling_remapped"],
                        "reason": reason,
                    }
                )
            else:
                rewrite_map[concept_name] = None
                rewrite_log.append(
                    {
                        "original": concept_name,
                        "rewritten": "null",
                        "sibling_original": entry["sibling_original"],
                        "sibling_remapped": entry["sibling_remapped"],
                        "reason": reason or "No reasonable rewrite found",
                    }
                )

    # Also log stranded concepts without siblings (not sent to LLM).
    for concept_name, kind, idx in stranded_without_siblings:
        rewrite_log.append(
            {
                "original": concept_name,
                "rewritten": "null",
                "sibling_original": "",
                "sibling_remapped": "",
                "reason": "No successfully-remapped sibling found",
            }
        )

    # Apply rewrites to each concept list.
    for kind_key in ("primitives", "operators", "identity_families"):
        original_list = concepts.get(kind_key, [])
        final: list[str] = []
        for concept_name in original_list:
            if concept_name in rewrite_map and rewrite_map[concept_name] is not None:
                final.append(rewrite_map[concept_name])  # type: ignore[arg-type]
            else:
                final.append(concept_name)
        rewritten[kind_key] = final

    return rewritten, rewrite_log
