# Concept Rewriter — Design Document

**Date:** 2026-02-22
**Status:** Approved for implementation
**Module:** `edge_finder/edge_finder/llm/concept_rewriter.py`

## 1. Problem Statement

The Edge Finder's concept generator proposes textbook-style type hierarchies (e.g., `DiscreteDerivative`, `DiscreteIntegral`, `ShiftOperator`). The concept remapper catches some naming mismatches by matching against search results (e.g., `DiscreteDiff → fwdDiff`). However, when a parent concept maps to null but a sibling concept maps to a real Mathlib name, dependent identity families are left stranded with their original fictional names (e.g., `DiscreteDerivative.chain` stays unchanged even though the related operator `DiscreteDiff` mapped to `fwdDiff`).

This inflates absence counts — the discrete calculus run reported 10/15 absent when the real gap is ~2 concepts.

## 2. Goals and Non-Goals

**Goals:**
- Rewrite stranded identity families and absent primitives/operators using evidence from successful remaps
- Reduce false-absence rate by propagating namespace knowledge from verified siblings
- Fit cleanly into the existing pipeline between remapping and verification

**Non-goals:**
- Replacing the concept remapper (it works well for direct matches)
- Rewriting concepts that the remapper already handled
- Guaranteeing perfect concept names (verification still validates downstream)

## 3. High-Level Architecture

```
concept_generator → search → remapper → [REWRITER] → verification
                                           ↑
                                    Uses remap_log to find
                                    sibling mappings and
                                    rewrites null concepts
```

## 4. Data Flow

**Input:**
- `concepts_remapped` — the remapped concepts dict (primitives, operators, identity_families)
- `remap_log` — list of `{original, remapped, reason}` dicts from the remapper
- `result_names` — all unique Mathlib declaration names from search results (same as remapper receives)

**Processing:**
1. Build a mapping of `original_concept → remapped_mathlib_name` from `remap_log` (excluding nulls)
2. Identify stranded concepts: those in `concepts_remapped` that were NOT successfully remapped (they still have their original generated names, because `concept_remapper.py` replaces null with original)
3. For each stranded concept, find its closest successfully-remapped sibling by checking shared stems (e.g., `DiscreteDerivative.chain` shares stem `Discrete` with `DiscreteDiff → fwdDiff`)
4. Build a single LLM prompt containing: (a) all stranded concepts, (b) their sibling mappings, (c) the actual Mathlib declaration names from search results
5. Ask the LLM to rewrite each stranded concept to its most likely Mathlib name, given the evidence
6. Return the rewritten concepts dict and a rewrite log for auditability

**Output:**
- `concepts_rewritten` — updated concepts dict with rewritten names
- `rewrite_log` — list of `{original, rewritten, sibling_evidence, reason}` dicts

## 5. Key Design Decisions

**Single LLM call, not per-concept.** All stranded concepts are batched into one prompt. At ~$0.002 this is negligible cost and avoids N separate API calls.

**Stem matching for sibling detection.** We use the first PascalCase word of each concept as its "stem" (e.g., `DiscreteDerivative` → `Discrete`, `FiniteSum` → `Finite`). A stranded concept's sibling is any successfully-remapped concept sharing the same stem. This is the same heuristic the candidate ranker already uses for clustering.

**Null = keep original.** If the LLM can't find a plausible rewrite, it returns null and the original name is preserved (same pattern as the remapper). Verification will then classify it as absent — which is correct for genuinely missing concepts.

**No new search queries.** The rewriter only uses existing search results. New LeanExplore queries happen in verification pass 2 (targeted search), which runs after this step.

## 6. Alternatives Considered

- **Option B (algorithmic namespace expansion):** Generate `fwdDiff_*` variants deterministically without LLM. Cheaper but can't handle non-obvious mappings like `DiscreteIntegral.product_rule → fwdDiff_mul`. The LLM's ability to reason about mathematical correspondence is the key advantage of Option A.
- **Extending the remapper prompt:** Could add sibling-evidence context to the existing remap prompt. Rejected because the remapper prompt is already large (up to 2000 declaration names) and the sibling reasoning is a distinct task.

## 7. Known Risks

- The LLM may produce plausible-looking but wrong names (e.g., `fwdDiff_chain` when the real name is `fwdDiff_comp`). This is acceptable because verification will catch it — a wrong guess that verification marks absent is no worse than the current state.
- If no concepts were successfully remapped, the rewriter has no sibling evidence and becomes useless. In this case it should be a no-op.

## 8. Critical Invariants

1. The rewriter must never modify concepts that the remapper already successfully handled
2. Output list lengths must match input list lengths (same as remapper contract)
3. The rewriter must be skippable (same `--skip-remap` flag disables both)
