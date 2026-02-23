"""Prompt builder functions for the edge finder LLM calls.

Contains prompt builders for concept generation (Module 1), concept re-mapping
(Iteration 5 grounding step), concept rewriting (Iteration 6 sibling propagation),
and pocket synthesis (Module 4). Also includes evidence summarization logic that
strips heavy fields (source_text) and truncates long strings to fit within the
LLM's context window. The prompts request structured JSON output.
"""

import json
from typing import Any


def build_concept_generator_prompt(theme: str) -> str:
    return f"""
You are building a Mathlib edge-finder run for the theme: {theme}.

Goal:
- Propose the core primitives, expected operators, and key lemma families that SHOULD exist in Mathlib for this theme.
- Focus on CONCRETE mathematical objects and operations, not abstract type hierarchies.
- Keep the output structured and inspectable.

Output JSON with keys:
- theme
- primitives: list of the core types, structures, or definitions relevant to this theme
- operators: list of key operations, functions, or constructions
- identity_families: list of theorem/lemma families (named by their mathematical content)
- candidate_namespaces: list of likely Mathlib namespaces
- search_queries: list of natural language queries to run in LeanExplore (CRITICAL — these drive what search results we get)

Naming conventions (IMPORTANT -- use Lean 4 / Mathlib style):
- Namespaces and type names use CamelCase: MonoidHom, Finset, GroupTheory, Subgroup.
- Lemma and theorem names use dot-qualified snake_case: MonoidHom.ker, Finset.sum_add_distrib, List.reverse_reverse.
- Prefer actual Lean 4 / Mathlib names when you know them. For example:
  - Use "fwdDiff" not "DiscreteDeriv" or "ForwardDifference" (Mathlib uses fwdDiff for the forward difference operator)
  - Use "MonoidHom.comp" not "compose_homomorphisms"
  - Use "Nat.choose" not "Binomial" or "BinomialCoefficient"
  - Use "Finset.sum" not "FiniteSum"
  - Use "Polynomial.derivative" not "PolyDeriv"
- If you are unsure of the exact Mathlib name, use your best guess at the qualified form (e.g., "Finset.sum_sigma" rather than "sum_sigma").
- Do NOT invent wrapper type names (DiscreteDerivative, DiscreteIntegral, ShiftOperator). Mathlib uses flat functions and lemma-name prefixes, not deep type hierarchies.
- Do NOT invent suffixes like _eq, _id, _test, _properties that are not part of Lean naming conventions.

Search query guidelines (CRITICAL):
- search_queries are the most important output — they determine what Mathlib declarations we find.
- Use diverse, specific queries. Include both concept names and mathematical descriptions.
- Good: ["forward difference operator", "fwdDiff Lean", "finite sum identities", "discrete product rule", "summation by parts"]
- Bad: ["discrete calculus", "discrete theorems"] (too vague)

Constraints:
- Do not claim anything exists in Mathlib; just propose what should exist.
- Keep each list concise (5-15 items).
- Prefer naming concrete operations (fwdDiff, Nat.choose, Finset.sum) over inventing abstract wrappers.
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

Your task: For each concept, find the best MATHEMATICALLY EQUIVALENT Mathlib declaration name from the search results list. Replace the concept name with the Mathlib name.

Rules:
- A valid match must represent the SAME mathematical object or theorem, not just share a word or prefix. For example:
  - "DiscreteDiff" -> "fwdDiff" is VALID (both are the forward difference operator)
  - "first_isomorphism_theorem" -> "QuotientGroup.quotientKerEquivRange" is VALID (same theorem)
  - "DiscreteDeriv" -> "DiscreteUniformity" is INVALID (derivative != uniformity, despite sharing "Discrete")
  - "Matrix" -> "DiscreteQuotient" is INVALID (matrices != quotient spaces)
  - "Func" -> "DiscreteTopology" is INVALID (generic functions != topology)
- Only match declarations that serve the same mathematical PURPOSE as the concept. Sharing a prefix (Discrete*, Finite*) is NOT sufficient.
- If a concept's name is already a valid Mathlib-style name and appears in the list (exact or close), keep it as-is.
- If no reasonable match exists in the list, set the value to null. This means the concept is genuinely not found. PREFER null over a bad match.
- Do NOT invent new Mathlib names. Only use names that appear EXACTLY in the provided list, or keep the original if it already appears.
- Preserve the list ordering. Each output list must have the same length as the input list.

IMPORTANT: When in doubt, output null. A null (concept not found) is far better than a wrong match (concept mapped to an unrelated declaration). Wrong matches corrupt the entire downstream analysis.

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


def build_concept_rewrite_prompt(
    theme: str,
    stranded_concepts: list[dict[str, str]],
    result_names: list[str],
) -> str:
    """Build a prompt that asks the LLM to rewrite stranded concepts.

    Stranded concepts are those the remapper could not match, but which have
    sibling concepts that DID match. The LLM receives the stranded concept,
    its mathematical meaning (inferred from the original name), and the actual
    Mathlib namespace of its successfully-remapped sibling. It then guesses the
    most likely Mathlib lemma name for the stranded concept.

    Args:
        theme: The investigation theme.
        stranded_concepts: List of dicts with keys:
            - "concept": the current (unremapped) concept name
            - "kind": primitive / operator / identity_family
            - "sibling_original": the original name of the sibling that was remapped
            - "sibling_remapped": the Mathlib name the sibling was remapped to
            - "sibling_module": the Mathlib module of the sibling (if known)
        result_names: All unique Mathlib declaration names from search results.
    """
    concepts_payload = json.dumps(stranded_concepts, ensure_ascii=True, indent=2)
    unique_names = sorted(set(result_names))
    if len(unique_names) > 2000:
        unique_names = unique_names[:2000]
    names_payload = json.dumps(unique_names, ensure_ascii=True)

    return f"""
You are a Lean 4 / Mathlib expert. You are helping to rewrite concept names that could not be matched to Mathlib declarations.

Theme: {theme}

Context: A previous step generated concept names for this theme and attempted to match them to actual Mathlib declaration names. Some concepts were successfully matched (e.g., "DiscreteDiff" matched to "fwdDiff" in Mathlib.Algebra.Group.ForwardDiff). However, other concepts sharing the same mathematical domain could NOT be matched — they are "stranded."

Your task: For each stranded concept below, use the evidence from its successfully-matched sibling to guess the most likely Mathlib declaration name. The sibling tells you which Mathlib namespace and naming convention to use.

Example:
- Stranded: "DiscreteDerivative.chain" (kind: identity_family)
- Sibling: "DiscreteDiff" was matched to "fwdDiff" (Mathlib.Algebra.Group.ForwardDiff)
- Reasoning: "DiscreteDerivative.chain" is the discrete chain rule. Since fwdDiff is the discrete derivative operator, the chain rule for fwdDiff would be named "fwdDiff_comp" (composition) following Mathlib naming conventions.
- Rewrite: "fwdDiff_comp"

Stranded concepts with sibling evidence:
{concepts_payload}

Mathlib declaration names from search results (for reference):
{names_payload}

Rules:
- Use the sibling's Mathlib name and module as your guide for the naming convention.
- If the stranded concept is a theorem/lemma about the sibling's operator, use the sibling's name as a prefix (e.g., fwdDiff_mul, fwdDiff_comp, Nat.choose_symm_diff).
- If the stranded concept is a primitive/type, look for the actual Mathlib type or predicate that serves the same role.
- If you find an EXACT match in the declaration names list, prefer that.
- If no reasonable rewrite exists, set the value to null.
- Do NOT invent names that don't follow Mathlib conventions.

Output JSON with key:
- rewrites: list of objects (same length and order as input), each with keys:
  - "concept": the original stranded concept name
  - "rewritten": the proposed Mathlib name (string or null)
  - "reason": brief explanation of the rewrite logic
"""


__all__ = [
    "build_concept_generator_prompt",
    "build_concept_remap_prompt",
    "build_concept_rewrite_prompt",
    "build_pocket_synthesis_prompt",
]
