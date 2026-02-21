"""Prompt builder functions for the edge finder LLM calls.

Contains prompt builders for concept generation (Module 1), concept re-mapping
(Iteration 5 grounding step), and pocket synthesis (Module 4). Also includes
evidence summarization logic that strips heavy fields (source_text) and truncates
long strings to fit within the LLM's context window. The prompts request
structured JSON output.
"""

import json
from typing import Any


def build_concept_generator_prompt(theme: str) -> str:
    return f"""
You are building a Mathlib edge-finder run for the theme: {theme}.

Goal:
- Propose the core primitives, expected intermediate abstractions, and high-level theorems that SHOULD exist for this theme.
- Keep the output structured and inspectable.

Output JSON with keys:
- theme
- primitives: list of short Lean-style identifiers or math objects
- operators: list of expected operators/abstractions
- identity_families: list of theorem/lemma families
- candidate_namespaces: list of likely Mathlib namespaces
- search_queries: list of natural language queries to run in LeanExplore

Naming conventions (IMPORTANT -- use Lean 4 / Mathlib style):
- Namespaces and type names use CamelCase: MonoidHom, Finset, GroupTheory, Subgroup.
- Lemma and theorem names use dot-qualified snake_case: MonoidHom.ker, Finset.sum_add_distrib, List.reverse_reverse.
- Prefer actual Lean 4 / Mathlib names when you know them. For example:
  - Use "MonoidHom.comp" not "compose_homomorphisms"
  - Use "List.get" not "list.nth"
  - Use "List.flatMap" not "list.concat_map"
  - Use "Nat.add_assoc" not "add_assoc_id"
- If you are unsure of the exact Mathlib name, use your best guess at the qualified form (e.g., "Finset.sum_sigma" rather than "sum_sigma").
- Do NOT invent suffixes like _eq, _id, _test, _properties that are not part of Lean naming conventions.

Constraints:
- Do not claim anything exists in Mathlib; just propose what should exist.
- Keep each list concise (5-15 items).
"""


def _summarize_search_results(responses: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Strip heavy fields (source_text) from search results to fit context."""
    summarized = []
    for resp in responses:
        results_summary = []
        for result in resp.get("results", []):
            results_summary.append(
                {
                    "name": result.get("name", ""),
                    "module": result.get("module", ""),
                    "docstring": (result.get("docstring") or "")[:200] or None,
                    "informalization": (result.get("informalization") or "")[:200]
                    or None,
                }
            )
        summarized.append(
            {
                "query": resp.get("query", ""),
                "count": resp.get("count", 0),
                "results": results_summary,
            }
        )
    return summarized


def build_concept_remap_prompt(
    theme: str,
    concepts: dict[str, Any],
    result_names: list[str],
) -> str:
    """Build a prompt that asks the LLM to re-map concept names to Mathlib names.

    The LLM receives the original concept lists and a flat list of Mathlib
    declaration names from search results. It returns the same JSON structure
    with concept names replaced by their best Mathlib match (or null if no
    reasonable match exists).
    """
    concepts_payload = json.dumps(
        {
            "primitives": concepts.get("primitives", []),
            "operators": concepts.get("operators", []),
            "identity_families": concepts.get("identity_families", []),
        },
        ensure_ascii=True,
        indent=2,
    )
    # Deduplicate and sort for readability; limit to avoid context overflow.
    unique_names = sorted(set(result_names))
    # 1500 unique names at ~40 chars each is ~60K chars (~17K tokens). Safe for
    # gpt-4o-mini (128K context). If somehow larger, truncate.
    if len(unique_names) > 2000:
        unique_names = unique_names[:2000]
    names_payload = json.dumps(unique_names, ensure_ascii=True)

    return f"""
You are a Lean 4 / Mathlib expert helping to ground concept names against actual Mathlib declarations.

Theme: {theme}

Below are two inputs:
1. A set of concept names (primitives, operators, identity families) generated for this theme.
2. A list of actual Mathlib declaration names found by searching for this theme.

Your task: For each concept, find the best matching Mathlib declaration name from the search results list. Replace the concept name with the Mathlib name.

Rules:
- If a concept clearly corresponds to a Mathlib declaration (even under a very different name), replace it with that declaration name. For example, "first_isomorphism_theorem" might map to "QuotientGroup.quotientKerEquivRange".
- If a concept's name is already a valid Mathlib-style name and appears in the list (exact or close), keep it as-is.
- If no reasonable match exists in the list, set the value to null. This means the concept is genuinely not found.
- Do NOT invent new Mathlib names. Only use names from the provided list or keep the original.
- Preserve the list ordering. Each output list must have the same length as the input list.

Concepts:
{concepts_payload}

Mathlib declaration names from search results:
{names_payload}

Output JSON with keys:
- primitives: list of strings or nulls (same length as input primitives)
- operators: list of strings or nulls (same length as input operators)
- identity_families: list of strings or nulls (same length as input identity_families)
- mapping: list of objects with keys "original", "remapped", "reason" (one per concept, in order: primitives then operators then identity_families)
"""


def build_pocket_synthesis_prompt(theme: str, evidence: dict[str, Any]) -> str:
    # Summarize responses to avoid blowing the context window.
    compact_evidence = {
        "responses": _summarize_search_results(evidence.get("responses", [])),
        "density_report": evidence.get("density_report", {}),
        "gap_report": evidence.get("gap_report", {}),
    }
    payload = json.dumps(compact_evidence, ensure_ascii=True, indent=2)
    return f"""
You are synthesizing a candidate mini-library pocket for the theme: {theme}.

Inputs (JSON):
{payload}

Output JSON with keys:
- theme
- pocket_summary: short paragraph
- proposed_abstractions: list
- candidate_lemmas: list of 10-25 lemma statements (plain text)
- dependency_sketch: list of edges (A -> B)
- justification: list of bullet points
- risk_level: one of Low / Moderate / High

Constraints:
- Use only the evidence in the inputs.
- Mark anything uncertain as "hypothesis".
"""


__all__ = [
    "build_concept_generator_prompt",
    "build_concept_remap_prompt",
    "build_pocket_synthesis_prompt",
]
