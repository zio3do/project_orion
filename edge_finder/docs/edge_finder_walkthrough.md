# Edge Finder -- Walkthrough Document

*Ownership transfer document per AGENTS.md Phase 3.*

---

## 1. What This Subsystem Does

The Edge Finder is a Python CLI pipeline that performs structural reconnaissance of Mathlib. Given a mathematical theme (e.g., "finite sums"), it uses an LLM to hypothesize what concepts, operators, and abstractions *should* exist, then searches Mathlib via the LeanExplore API to assess what actually does exist. An LLM-based concept re-mapping step (Iteration 5) grounds the generated concept names against actual Mathlib declaration names observed in search results. It then verifies each (optionally remapped) concept individually against search results (classifying as verified, partial, absent, or name_mismatch), computes structural density metrics (namespace distribution, operator coverage, module spread) as informational context, and classifies potential gaps using verification coverage as the sole gap signal. All search queries, results, re-mapping logs, and per-concept verification evidence are logged for human audit.

---

## 2. Mental Model

Think of the Edge Finder as a five-phase process:

1. **Hypothesize:** An LLM generates a structured "wish list" of mathematical objects for a theme, using Lean 4 / Mathlib naming conventions.
2. **Search:** The wish-list's search queries run against Mathlib's semantic search.
3. **Ground:** An LLM re-maps the generated concept names to actual Mathlib declaration names found in the search results (Iteration 5). This addresses the naming convention mismatch between textbook-style names and Mathlib's qualified identifiers.
4. **Verify:** Each (remapped) concept is individually matched against the search results and classified (verified, partial, absent, name_mismatch).
5. **Analyze:** Aggregate metrics and heuristic classifiers assess structural density and gap patterns.

The key mental model is: **the system is trying to measure the distance between "what should exist" and "what does exist."** The concept re-mapping step (Iteration 5) narrows this distance by aligning generated names with actual Mathlib names before verification. The per-concept verification then measures coverage at the individual concept level. As of Iteration 4, verification coverage is the sole gap signal -- density metrics are computed for human inspection but do not produce gap claims. The gap classifier reports `concept_coverage_gap` (tiered by coverage ratio), `density_context` (informational), `well_covered` (positive finding), or `insufficient_signal` (fallback).

A useful analogy: imagine you have a checklist of ingredients for a recipe, and you're searching a warehouse. The system reports checklist-style results: "flour: found, sugar: found, cardamom: not found, saffron: found but labeled 'crocus stigma'." Pass 1 searches the warehouse using broad queries ("baking supplies"); pass 2 goes back and searches specifically for each missing ingredient by name and plausible shelf locations. In the "finite sums" test theme, pass 1 achieved 66.7% coverage; pass 2 raised it to 100% by finding all 4 "missing" identity families under their qualified Mathlib names.

---

## 3. Directory Structure

```
edge_finder/edge_finder/
    __init__.py          Empty package marker
    __main__.py          Entry point: calls cli.main()
    cli.py               Pipeline orchestrator (~255 lines)
    config.py            Constants and RunMetadata dataclass (15 lines)
    prompts.py           Prompt builder functions (~167 lines)
    sample_concepts.json Cached test fixture for dry-run mode

    llm/
        __init__.py
        client.py              OpenAI wrapper with retry/truncation (79 lines)
        concept_generator.py   Module 1: theme -> concepts JSON (14 lines)
        concept_remapper.py    Iteration 5: remap concept names to Mathlib declarations (~92 lines)
        pocket_synthesis.py    [REMOVED FROM SCOPE] Old Module 4: evidence -> pocket blueprint (19 lines)

    search/
        __init__.py
        leanexplore.py    Async wrapper with retry: search_queries() + search_single() (~155 lines)
        models.py         SearchResult/SearchResponse dataclasses (113 lines)
        logger.py         JSONL search log writer (45 lines)

    verification/
        __init__.py       Module 2: two-pass verification layer (~468 lines)
                          Data model (VerificationStatus, ConceptKind, MatchEvidence,
                          VerificationEntry, VerificationReport), matching heuristics
                          (_find_matches, _classify_status), pass 1 (verify_concepts),
                          targeted query generation (generate_targeted_queries),
                          pass 2 refinement (refine_verification)

    analysis/
        __init__.py
        density.py        Namespace stats, spread ratios, operator hits (179 lines)
        heuristics.py     Verification-only gap classification (4 categories) (219 lines)

    output/
        __init__.py
        writer.py         JSON report serializer (43 lines)
```

**Run outputs** go to `edge_finder/runs/edge_finder/run_<timestamp>_<theme>/`.

---

## 4. Call Graph

```
cli.main()
    |
    +-- _load_dotenv(".env")
    |
    +-- generate_concepts(theme, model)          [Module 1]
    |       |
    |       +-- LlmClient.complete_json(prompt)
    |               |
    |               +-- OpenAI API call
    |
    +-- search_queries(queries, config)          [Module 2 - theme search]
    |       |
    |       +-- _search_with_retry(client, query, ...)  [for each query]
    |               |
    |               +-- ApiClient.search(query)  [with retry on 5xx]
    |
    +-- log_search_response(path, response)      [for each response]
    |
    +-- remap_concepts(concepts, responses, model)  [Iteration 5 - name grounding]
    |       |  (skipped if --skip-remap or --dry-run)
    |       +-- build_concept_remap_prompt(theme, concepts, result_names)
    |       +-- LlmClient.complete_json(prompt)
    |       |       +-- OpenAI API call
    |       +-- returns (remapped_concepts, mapping_log)
    |
    +-- verify_concepts(concepts_for_verification, responses)  [Module 2 - pass 1]
    |       |
    |       +-- extract_concepts(concepts)
    |       |       +-- pulls primitives, operators, identity_families
    |       +-- _find_matches(concept, unique_results)  [for each concept]
    |       |       +-- checks: exact, qualified_suffix, substring, informalization
    |       +-- _classify_status(matches)  [for each concept]
    |       +-- returns initial VerificationReport
    |
    +-- refine_verification(report, concepts_for_verification, search_fn)  [Module 2 - pass 2]
    |       |  (skipped if --skip-targeted-search)
    |       +-- [for each absent/partial concept:]
    |       |       +-- generate_targeted_queries(concept, candidate_namespaces)
    |       |       +-- search_fn(query)  [for each targeted query]
    |       |       |       +-- search_single(query, config)
    |       |       |               +-- _search_with_retry(client, query, ...)
    |       |       |                       +-- ApiClient.search(query)  [with retry on 5xx]
    |       |       +-- _find_matches(concept, targeted_results)
    |       |       +-- merge matches, _classify_status(combined)
    |       +-- returns (refined VerificationReport, targeted SearchResponses)
    |
    +-- log_search_response(path, response)      [for each targeted response]
    |
    +-- compute_density_report(all_responses)     [Module 3]
    |       |  (all_responses = theme + targeted)
    |       +-- _namespace_of(name)  [for each result]
    |       +-- _operator_candidates(results)
    |       +-- _namespace_depth(name)  [for each result]
    |
     +-- classify_gaps(density_report, verification_report, responses)  [Module 3]
     |       |
     |       +-- _compute_search_coverage(responses)
     |       +-- concept_coverage_gap check (from verification, sole gap signal)
     |       +-- _downgrade_confidence() if search coverage < 0.7
     |       +-- density_context (informational, always present)
    |
    +-- [Module 4: Pocket Candidate Ranking — designed, not yet implemented]
    |       See candidate_ranker/edge_finder_pocket_candidates.md
    |       Will call: rank_candidates(concepts, verification, density, gap, responses)
    |       No API calls — purely algorithmic (namespace clustering + scoring)
    |
    +-- write_run_report(...)                     [Output]
```

All calls are synchronous except `search_queries()` and `refine_verification()`, which are async (run via `asyncio.run()`). Within both, each query is awaited sequentially (no concurrent requests). The `remap_concepts()` call is synchronous (uses `LlmClient.complete_json()`).

---

## 5. Execution Lifecycle

### Invocation

```bash
PYTHONPATH=edge_finder python -m edge_finder --theme "finite sums"
```

### Step-by-step

1. **Parse args.** Theme is required. Optional: `--model`, `--search-limit`, `--dry-run`, `--concepts-path`, `--pocket-path` (deprecated, old Module 4), `--output-dir`, `--version`, `--skip-targeted-search`, `--skip-remap`.

2. **Load `.env`.** Custom dotenv loader at `cli.py:60-73`. Sets env vars only if not already set. Reads `OPENAI_API_KEY` and `LEANEXPLORE_API_KEY`.

3. **Create run directory.** `edge_finder/runs/edge_finder/run_<timestamp>_<theme>/`. Timestamp format: `%Y-%m-%d_%H%M%S` (24-hour, no colons).

4. **Generate or load concepts.** In normal mode, calls OpenAI. In dry-run mode, loads from `--concepts-path`. Writes `concepts.json` to run dir.

5. **Extract search queries.** From `concepts["search_queries"]`. Fails if empty.

6. **Run LeanExplore searches.** One API call per query, sequential. Each returns up to `--search-limit` results (default 20). Results are wrapped in `SearchResponse`/`SearchResult` dataclasses.

7. **Log searches.** Each response appended to `search_log.jsonl`. Also writes `search_responses.json` (full dump).

8. **Re-map concept names (Iteration 5).** Unless `--skip-remap` or `--dry-run` is set, `remap_concepts()` collects all unique declaration names from the search results, then asks the LLM to match each generated concept name to the closest Mathlib declaration (or null if genuinely absent). Null values (including the string `"null"`) fall back to the original name. Writes `concepts_remapped.json` and `remap_log.json` to the run directory. The remapped concepts are used for all downstream verification steps.

9. **Verify concepts (pass 1: theme-level).** `verify_concepts()` extracts each primitive, operator, and identity family from the (optionally remapped) concepts JSON, matches each against all deduplicated search results using name-based heuristics (exact, qualified_suffix, substring, informalization), classifies each as verified/partial/absent/name_mismatch, and produces an initial `VerificationReport`.

10. **Refine verification (pass 2: targeted search).** Unless `--skip-targeted-search` is set, `refine_verification()` iterates over each concept classified as `absent` or `partial` in the pass 1 report. For each, it calls `generate_targeted_queries()` to produce 1-4 deterministic queries (bare name, namespace-prefixed variants, space-separated semantic variant), searches each via `search_single()`, merges new matches with originals (deduplicating by `result_name`), and re-classifies. Targeted search responses are logged to `search_log.jsonl` and appended to `all_responses`. The refined report replaces the initial one. Writes `verification.json` to run dir.

11. **Compute density.** `compute_density_report()` aggregates all results (theme + targeted) into namespace counts, module lists, operator hits, spread ratios, namespace depths.

12. **Classify gaps.** `classify_gaps()` receives the `DensityReport`, `VerificationReport`, and raw `SearchResponse[]` list. Verification coverage is the sole gap signal: `concept_coverage_gap` fires when coverage < 0.7, with tiered confidence (high/moderate/low) calibrated from empirical data. Search coverage (fraction of queries returning results) downgrades confidence one tier if < 0.7 (API failures make absence unreliable). Density metrics are reported as `density_context` (informational). If coverage >= 0.7, a `well_covered` positive finding is produced.

13. **[REMOVED FROM SCOPE] Pocket synthesis.** The old Module 4 (LLM-based pocket synthesis) has been removed from the Edge Finder's scope. A new Module 4 (Pocket Candidate Ranking) has been designed but not yet implemented. See `candidate_ranker/edge_finder_pocket_candidates.md`. When implemented, this step will algorithmically cluster and score absent/partial concepts to produce `candidates.json`. No LLM call is involved.

14. **Write run report.** `run_<date>_<theme>.json` containing all artifacts including verification report.

15. **Print output path.** The only user-facing output is the path to the run report.

### Exit codes

The pipeline raises `RuntimeError` or `ValueError` on failure. No structured error handling or partial-run recovery.

---

## 6. Annotated Key Functions

### `cli.py:103-254` -- `main()`

The orchestrator. Notable characteristics:
- Monolithic: all pipeline steps are in one function with no abstraction boundaries.
- The `evidence` dict at line 208 is assembled ad-hoc from all_responses, verification_report, density_report, and gap_report. This was the input to the old pocket synthesis step (now removed from scope). When the new Module 4 is implemented, the evidence assembly will likely be replaced by explicit function arguments.
- The dry-run branching (lines 120-131, 214-237) interleaves with the normal flow rather than being a separate code path.
- Concept re-mapping at lines 157-174 (skipped if `--skip-remap` or `--dry-run`). Writes `concepts_remapped.json` and `remap_log.json`.
- Pass 1 verification at line 177; pass 2 targeted refinement at lines 179-197 (skipped if `--skip-targeted-search`). `all_responses` (line 180) accumulates both theme and targeted responses for downstream density analysis.
- Verification step runs after re-mapping and search logging, before density analysis.

### `verification/__init__.py:276-326` -- `verify_concepts()`

The per-concept verification entry point (pass 1). Flattens all search results across all queries, deduplicates by `declaration_id`, then for each concept calls `_find_matches()` and `_classify_status()`. Returns a `VerificationReport` with one `VerificationEntry` per concept. Each entry records the concept name, kind, status, match evidence, and which queries were searched.

### `verification/__init__.py:175-244` -- `_find_matches()`

The matching heuristic. For each search result, checks four match types in order of strength: exact name match, qualified suffix (e.g., `Finset.sum` matches concept `sum`), substring in name, informalization/docstring match. Returns a list of `MatchEvidence` objects. The `continue` after exact/qualified_suffix/substring means only the strongest match type per result is recorded.

### `density.py:134-179` -- `compute_density_report()`

The core analysis function. Iterates all search results (theme + targeted), extracts 2-level namespaces (e.g., `Finset.sum` from `Finset.sum.comm`) and modules, computes aggregate statistics. Operator detection uses 28 suffix patterns covering aggregation, functorial, algebraic, lattice, set-theoretic, and composition operators.

### `verification/__init__.py:334-383` -- `generate_targeted_queries()`

Deterministic query generator for per-concept targeted search (no LLM). Given a concept name and list of candidate namespaces, produces 1-4 queries: (1) the bare concept name, (2) namespace-prefixed variants using only top-level namespaces (skips sub-namespaces like `Finset.sum` to avoid nonsensical `Finset.sum.sum_add_distrib`, and skips self-prefixing to avoid `BigOperators.BigOperators`), (3) a space-separated variant for semantic search if the concept contains underscores. Deduplicates by lowercased string.

### `verification/__init__.py:386-467` -- `refine_verification()`

The pass 2 verification entry point (async). Iterates each entry in the initial `VerificationReport`; skips already-`verified` or `name_mismatch` concepts. For each `absent`/`partial` concept: generates targeted queries via `generate_targeted_queries()`, searches each via the injected `search_fn` (a closure over `search_single()`), deduplicates targeted results by `declaration_id`, runs `_find_matches()` against the targeted results, merges new matches with originals (deduplicating by `result_name`), and re-classifies via `_classify_status()`. Returns a `(refined_report, targeted_responses)` tuple. The caller is responsible for logging the targeted responses.

### `search/leanexplore.py:87-125` -- `search_single()`

Async single-query search used by the targeted refinement step. Creates a fresh `ApiClient` per call (acceptable for the typically < 100 targeted queries per run). Delegates to `_search_with_retry()` which retries up to 2 times with exponential backoff (1s, 2s) on HTTP 5xx errors. Key design choice: catches all exceptions after retry exhaustion and returns an empty `SearchResponse` rather than crashing, since targeted queries may hit edge cases (e.g., `sum_sigma` triggers LeanExplore 500 errors).

### `llm/concept_remapper.py:25-94` -- `remap_concepts()`

Iteration 5 concept name grounding. Collects all unique declaration names from theme-level search results, then asks the LLM to match each generated concept to the closest Mathlib name. Returns a tuple of (remapped concepts dict, mapping log). Key edge cases handled: (1) empty search results returns concepts unchanged, (2) LLM returns different-length list falls back to originals for mismatched portion, (3) the string `"null"` (not JSON null) is treated as absent and falls back to the original name. This last case was a critical bug fix -- LLMs sometimes emit `"null"` as a JSON string, causing nonsense targeted queries like `Subgroup.null`.

### `heuristics.py:77-218` -- `classify_gaps()`

Verification-only gap classifier (redesigned in Iteration 4). Accepts three inputs: `DensityReport` (informational context), optional `VerificationReport` (gap detection), and optional `SearchResponse[]` list (search coverage computation). Produces up to three findings:

1. **`concept_coverage_gap`** (sole gap signal): fires when verification coverage < 0.7. Confidence is tiered by empirically calibrated thresholds: `high` (coverage < 0.3), `moderate` (< 0.5), `low` (< 0.7). If search coverage is below 0.7 (many queries returned errors), confidence is downgraded one tier via `_downgrade_confidence()`.
2. **`density_context`** (informational): always present when declarations exist. Reports aggregate metrics (declarations, namespaces, modules, spread ratio, operator hits). Not a gap claim.
3. **`well_covered`**: fires when verification coverage >= 0.7. Positive confirmation the theme is well-represented.
4. **`insufficient_signal`**: fallback for zero declarations or missing verification data.

Previous density-derived categories (`missing_operator_abstraction`, `namespace_fragmentation`, `middle_layer_gap`, `missing_thematic_file`) were removed in Iteration 4 after calibration showed they had zero discriminative power across themes.

### `client.py:37-66` -- `LlmClient.complete_json()`

OpenAI call with retry logic. Handles context length overflow by truncating the prompt at 50% and retrying. Handles rate limits with exponential backoff. Returns raw JSON string. Uses the `responses.create` API (not `chat.completions`), with `text.format.type = "json_object"` to enforce JSON output.

### `prompts.py:29-51` -- `_summarize_search_results()`

**[DEPRECATED — part of old Module 4 (Pocket Synthesis), removed from scope.]** Evidence compression for the pocket synthesis prompt. Strips `source_text` and truncates `docstring` and `informalization` to 200 chars each. This function is retained in the codebase but is no longer called by the active pipeline. It may be removed in a future cleanup pass.

---

## 7. Critical Invariants

1. **Search queries come from the Concept Generator, not hardcoded.** The pipeline must not bypass the LLM hypothesis step with manual queries -- that would defeat the purpose of systematic reconnaissance.

2. **Every search query and its results are logged.** The `search_log.jsonl` file must contain one entry per query. This is the audit trail.

3. **The GapReport requires verification evidence for gap claims.** As of Iteration 4, `concept_coverage_gap` is the sole gap signal and requires a `VerificationReport`. Density metrics are reported as informational `density_context` but never produce gap claims. The LLM generates hypotheses (Module 1) and the concept re-mapping step (Iteration 5) grounds names against Mathlib declarations, but Modules 2-3 must be grounded in API evidence. Module 4 (Pocket Candidate Ranking, not yet implemented) is purely algorithmic — no LLM involved.

4. **Frozen dataclasses are immutable.** All model objects (`SearchResult`, `SearchResponse`, `DensityReport`, `GapReport`, `GapFinding`, `NamespaceStats`, `RunMetadata`, `SearchLogEntry`, `MatchEvidence`, `VerificationEntry`, `VerificationReport`) are `@dataclass(frozen=True)`. Do not add mutable state to these.

5. **The `.env` file is never committed.** It contains API keys. (Enforced by `.gitignore`.)

---

## 8. Things That Must Not Be Broken

- **Search logging.** If the JSONL log is lost or incomplete, the entire run becomes unauditable.
- **The concept -> search -> verify -> analysis pipeline order.** Concepts must be generated before search; search must complete before verification; verification must complete before density analysis. The current sequential flow in `main()` enforces this.
- **Per-concept verification evidence chain.** Each `VerificationEntry` records match evidence linking the concept to specific search results. Breaking `_find_matches()` or `_classify_status()` silently degrades the entire verification layer.
- **JSON serialization round-trip.** Every dataclass has `to_dict()` methods. The `VerificationReport.to_dict()` must remain consistent with the data model. (Note: `VerificationEntry` and `VerificationReport` do not have `from_dict()` methods yet.)
- **The dry-run path.** This is the only way to test the pipeline without API costs. Breaking it removes the ability to iterate on analysis logic cheaply.

---

## 9. Most Dangerous Refactor Mistakes

1. **Making search queries concurrent without rate limiting.** The LeanExplore API may have rate limits. The current sequential approach is safe. Adding concurrency requires explicit throttling.

2. **Changing `_namespace_of()` without updating downstream consumers.** The namespace extraction function is used in density computation and affects all namespace-related metrics. It was changed from 1-level to 2-level in Iteration 3, which changed every DensityReport. Any further changes (e.g., to 3-level) would have the same cascading effect. Density metrics are now informational-only (not gap signals), so the impact is reduced but still affects human-facing reports.

3. **Implementing Module 4 (Pocket Candidate Ranking) without following the design doc.** The design doc (`candidate_ranker/edge_finder_pocket_candidates.md`) specifies the clustering algorithm, scoring weights, and output schema. Deviating without updating the design doc first will create doc-code drift that undermines the docs-first development protocol.

4. **Breaking the concept re-mapping → verification ordering.** Re-mapping must happen after theme-level search (needs search results to match against) and before pass 1 verification. Moving it after verification would defeat its purpose. This is also listed as item 7 below but bears repeating because it is the most likely source of subtle regressions.

5. **Breaking the `from_lean_explore()` adapter in `SearchResult`.** This is the bridge between the `lean_explore` library's response objects and the edge finder's internal models. The adapter uses `getattr()` with fallbacks because the upstream API may evolve.

6. **Removing the `"null"` string check in `concept_remapper.py`.** LLMs sometimes emit the string `"null"` instead of JSON `null`. Without the `value.lower() == "null"` guard (line 83), null-intended values become the literal string `"null"`, which propagates through as concept names (e.g., `Subgroup.null` in targeted queries). This was a real bug that caused 131/131 targeted query failures in early Iteration 5 runs.

7. **Changing the concept re-mapping step order.** Re-mapping must happen after theme-level search (needs search results to match against) and before pass 1 verification (verification operates on remapped names). Moving it after verification would defeat its purpose. Removing it would regress coverage on themes with naming mismatches (e.g., group homomorphisms would drop from 0.72 to ~0.26).

---

## 10. Open Questions and Technical Debt

### Open questions

- **How effective are per-concept targeted queries?** Answered by Iteration 2: very effective. Coverage jumped from 0.667 (pass 1 only) to 1.0 (pass 1 + pass 2) on the "finite sums" test theme. All 4 previously-absent identity families were found via targeted queries, and 1 partial concept was upgraded to verified. 16 targeted API calls sufficed. This largely resolves the false-absence problem for concepts that exist under qualified names. Open sub-question: will this hold for themes where Mathlib's naming is less systematic?
- **What constitutes "partial" vs. "absent"?** Still relevant. Iteration 2 reduced the number of `partial` results (from 2 to 1 in the test theme), but the core question remains: substring matching can be too generous. The remaining `partial` (`BigOperators`) is correct -- it's a namespace/import, not a declaration. But other themes may produce more ambiguous cases.
- **Should the density/gap analysis consume verification data?** Answered by Iterations 3-4. Iteration 3 made gap classification verification-aware. Iteration 4 went further: calibration against 6 themes showed density-derived gap heuristics have zero discriminative power (LeanExplore returns fixed-size result sets). Verification coverage is now the sole gap signal; density metrics are informational only.
- **At what point is the edge finder "good enough" to select a pocket?** The outline describes Phase C as "select pocket" -- what evidence threshold justifies that transition?

### Technical debt

- **No tests.** The entire pipeline is untested. Any refactoring risks silent regressions.
- **No `from_dict()` on verification types.** `VerificationEntry` and `VerificationReport` have `to_dict()` but no deserialization. This means verification results cannot be reloaded from disk.
- **Pocket synthesis prompt does not reference Iteration 4 gap categories.** [REMOVED FROM SCOPE — old Module 4 (Pocket Synthesis) is no longer part of the Edge Finder pipeline. Replaced by Pocket Candidate Ranking.]
- **LLM concept naming quality partially addressed by Iteration 5.** The improved prompt and concept re-mapping raised average coverage from 0.33 to 0.60 across 6 themes. However, ~20% of changed remappings are inaccurate (mapping to semantically adjacent but wrong declarations, e.g., `List.filter` -> `List.filterMap`). A stronger model, post-hoc validation step, or few-shot examples in the remap prompt could improve this further.
- **`verification/__init__.py` is 468 lines.** Approaching the 500-line threshold where splitting into submodules should be considered.
- **Duplicate concepts in generation.** The LLM sometimes generates the same concept in both `operators` and `identity_families` lists. Could add deduplication or prompt instructions to prevent this.
- **Pocket synthesis is not grounded in verification data.** [REMOVED FROM SCOPE — old Module 4 (Pocket Synthesis) is no longer part of the Edge Finder pipeline. Replaced by Pocket Candidate Ranking.]
- **New Module 4 (Pocket Candidate Ranking) designed but not yet implemented.** See `candidate_ranker/edge_finder_pocket_candidates.md`. Implementation target: `analysis/candidates.py` (~150-200 lines). When implemented, will also require updating `cli.py` to call the new module instead of `synthesize_pocket()`, and updating `output/writer.py` to serialize `candidates.json`.
