# Verification Layer — Ownership Transfer Document

*Phase 3 artifact per AGENTS.md. Written as an onboarding guide for an engineer who will maintain
or extend the verification subsystem independently.*

---

## 1. What This Subsystem Does

The verification layer (Module 2) is the evidence backbone of the Edge Finder pipeline. Its job is
to answer a single question: **does a hypothesized mathematical concept actually exist in Mathlib?**

It receives two inputs — a structured list of LLM-generated concept names (primitives, operators,
identity families) and a collection of LeanExplore search results — and produces a
`VerificationReport` that classifies each concept as `verified`, `partial`, `absent`, or
`name_mismatch`, with full match evidence linking each classification back to specific Mathlib
declarations.

The subsystem runs in two passes:

- **Pass 1 (theme-level):** matches all concepts against the broad theme search results in a single
  pass. Fast, no additional API calls.
- **Pass 2 (targeted):** for each concept that is still `absent` or `partial`, generates
  deterministic targeted queries and searches LeanExplore individually. Re-classifies with combined
  evidence.

As of Iteration 5, concepts optionally pass through an LLM-based re-mapping step before entering
the verification layer. The verification code itself is name-agnostic — it operates on whatever
strings it receives.

---

## 2. Mental Model for Understanding It

Think of Pass 1 as casting a wide net over a warehouse and then checking your checklist against
everything you caught. Pass 2 is going back into the warehouse and searching specifically for each
item you missed, shelf by shelf.

The matching logic works on **name string similarity**, not semantic meaning. This is intentional —
semantic matching is delegated to LeanExplore's search model. The verification layer's job is
precise classification of the results LeanExplore returns.

The four match types form a hierarchy of confidence:

```
exact  >  qualified_suffix  >  substring  >  informalization
  ↓              ↓                  ↓               ↓
verified       verified           partial       name_mismatch
```

Only the strongest match type per result is recorded. The status of a concept is determined by the
strongest match type across **all** its results combined.

A key invariant: **the classification is conservative**. Substring matches are classified as
`partial`, not `verified`, because `List.filterMap` matching concept `filter` is not the same
declaration. This means some true positives are under-classified, but no false verification claims
are made at the `verified` level without an exact or qualified-suffix name match.

---

## 3. Directory Structure

```
edge_finder/edge_finder/verification/
    __init__.py    The entire subsystem (468 lines)
                   Contains: data model, matching heuristics, two public pass functions,
                   targeted query generator, pass 2 refinement async function.
```

There is no further subdivision. The single file is approaching the AGENTS.md 500-line split
threshold but has not crossed it. See Section 10 for the refactor plan.

**Upstream dependencies (inputs to this subsystem):**

```
edge_finder.search.models    SearchResponse, SearchResult — the search result dataclasses
edge_finder.llm.concept_remapper   (upstream, not in this module) — optionally transforms
                                    concept names before verify_concepts() is called
```

**Downstream consumers (outputs from this subsystem):**

```
cli.py               drives both passes, logs targeted responses, passes report to density/gap
analysis/heuristics.py   consumes VerificationReport.coverage_ratio as the sole gap signal
output/writer.py     serializes VerificationReport via to_dict() into the run report
```

---

## 4. Call Graph

```
cli.main()
  │
  ├─► verify_concepts(concepts_for_verification, responses)          [pass 1]
  │       │
  │       ├─ extract_concepts(concepts)
  │       │      pulls (name, ConceptKind) tuples from primitives / operators / identity_families
  │       │
  │       ├─ [flatten + deduplicate all SearchResults across all responses]
  │       │
  │       └─ for each concept:
  │              _find_matches(concept, unique_results)  →  list[MatchEvidence]
  │              _classify_status(matches)               →  VerificationStatus
  │              → VerificationEntry
  │          → VerificationReport (initial)
  │
  └─► refine_verification(initial_report, concepts, search_fn)       [pass 2, async]
          │
          └─ for each entry where status in {absent, partial}:
                 generate_targeted_queries(concept, candidate_namespaces)
                 │   (deterministic, no LLM)
                 │
                 for each targeted query:
                     await search_fn(query)    ← closure over search_single()
                     → SearchResponse  (logged by cli.py after return)
                 │
                 _find_matches(concept, unique_targeted_results)
                 merge with original entry.matches (deduplicate by result_name)
                 _classify_status(combined_matches)
                 → refined VerificationEntry
          → (VerificationReport refined, list[SearchResponse] new_responses)
```

`verify_concepts()` is synchronous. `refine_verification()` is `async` because it calls
`search_fn` which is an async closure over `search_single()`. Both are run via `asyncio.run()`
in `cli.py`.

---

## 5. Execution Lifecycle Walkthrough

### Pass 1: `verify_concepts()`

1. **Flatten results.** All `SearchResult` objects from all `SearchResponse` objects are collected
   into a single list. This means a result that appeared in three different query responses is
   included three times at this point.

2. **Deduplicate.** Results are deduplicated by `declaration_id`. A Mathlib declaration that
   appears in multiple query results is counted once.

3. **Extract concepts.** `extract_concepts()` pulls the three verifiable lists from the concepts
   dict: `primitives`, `operators`, `identity_families`. `candidate_namespaces` and
   `search_queries` are intentionally excluded — they are metadata, not claims.

4. **Match and classify.** For each concept, `_find_matches()` iterates over all unique results
   and produces a list of `MatchEvidence` objects. `_classify_status()` then determines the
   overall `VerificationStatus` from that evidence list.

5. **Build report.** One `VerificationEntry` per concept, all assembled into a
   `VerificationReport`.

### Pass 2: `refine_verification()`

1. **Skip already-resolved concepts.** Entries with `verified` or `name_mismatch` status are
   passed through unchanged. Only `absent` and `partial` entries proceed.

2. **Generate targeted queries.** `generate_targeted_queries()` produces 1–5 queries per concept:
   - The bare concept name (always included).
   - Namespace-prefixed variants: only top-level candidate namespaces (no dots in namespace name),
     and only if the concept itself is unqualified (no dots). This prevents nonsense like
     `Finset.sum.GroupHom.ker`.
   - A space-separated variant if the concept contains underscores, for LeanExplore's semantic
     search path (e.g., `sum add distrib` may surface what `sum_add_distrib` misses).
   - All queries are deduplicated by lowercased string.

3. **Search and merge.** Each targeted query is awaited via `search_fn`. Results are deduplicated
   by `declaration_id`, matched via `_find_matches()`, then merged with the original entry's
   matches (deduplicating by `result_name`).

4. **Re-classify.** `_classify_status()` runs on the combined evidence. A concept that was
   `absent` in pass 1 may become `verified` in pass 2 if the targeted query returns an exact match.

5. **Return.** A new `VerificationReport` (replacing the initial one) and the list of new
   `SearchResponse` objects. **The caller (`cli.py`) is responsible for logging the new
   responses** — `refine_verification()` does not log anything itself.

---

## 6. Annotated Excerpts of Key Functions

### `_find_matches()` — lines 175–244

```python
def _find_matches(concept: str, results: list[SearchResult]) -> list[MatchEvidence]:
```

The matching engine. Four match types are checked in order of strength. A `continue` after
`exact`, `qualified_suffix`, and `substring` ensures only the strongest match type per result
is recorded. The `informalization` path is reached only if the result's name does not match at all.

**Critical detail:** the `qualified_suffix` check is `.lower()` on both sides and checks for
`.{concept}` (with a leading dot). This means `Finset.sum` matches concept `sum`, but
`finsum_add_distrib` does not match `sum` (no leading dot, so it falls to `substring`). This
is intentional — `qualified_suffix` is meant to capture the standard Mathlib pattern of
`Namespace.declaration_name`.

**Edge case:** a concept like `Finset.sum` will match result `Finset.sum` via `exact`, and also
match result `Finset.sum.comm` via `substring` (since `finset.sum` appears in `finset.sum.comm`).
The `continue` after `exact` prevents the `substring` match from also being recorded for
`Finset.sum` itself, but `Finset.sum.comm` still gets a `substring` entry. This is correct
behavior.

### `_classify_status()` — lines 247–268

```python
def _classify_status(matches: list[MatchEvidence]) -> VerificationStatus:
```

Priority rules:
1. Any `exact` or `qualified_suffix` → `verified`
2. Any `substring` (and no stronger) → `partial`
3. Any `informalization` (and nothing else) → `name_mismatch`
4. Empty matches → `absent`

**Why not a single `partial` for `informalization`?** `name_mismatch` is a distinct signal: it
means the concept appears to be described in Mathlib under a different declaration name. It is
more actionable than `absent` — it suggests the concept exists but with a naming gap. The gap
classifier and pocket synthesis can treat it differently.

### `generate_targeted_queries()` — lines 334–383

```python
def generate_targeted_queries(concept: str, candidate_namespaces: list[str]) -> list[str]:
```

No LLM call. Purely deterministic string manipulation. The logic for skipping sub-namespaces
(`"." not in ns`) was added after observing that candidate namespaces like `Finset.sum` would
generate nonsense queries like `Finset.sum.sum_add_distrib`.

The self-prefixing guard (`ns.lower() != concept.lower()`) prevents `BigOperators.BigOperators`.

**Typical output for concept `"sum_add_distrib"` with namespaces `["Finset", "Finset.sum", "BigOperators"]`:**
```
["sum_add_distrib", "Finset.sum_add_distrib", "BigOperators.sum_add_distrib", "sum add distrib"]
```

### `refine_verification()` — lines 386–467

```python
async def refine_verification(
    initial_report: VerificationReport,
    concepts: dict[str, Any],
    search_fn: Callable[[str], Any],
) -> tuple[VerificationReport, list[SearchResponse]]:
```

The `search_fn` parameter is a dependency injection point. In production, `cli.py` passes a
closure over `search_single()` with the current config bound. In tests, a mock function can be
injected. This is the correct abstraction boundary — the verification layer does not know which
search backend is in use.

**Important:** new responses are accumulated in `new_responses` and returned to the caller.
The caller owns logging. If a caller discards the second return value, the targeted searches
will be silently unlogged — this is a latent correctness risk.

---

## 7. Critical Invariants

1. **Deduplication by `declaration_id` in pass 1.** All results are deduplicated before matching.
   A concept that appears in 10 query result sets is only matched once. Removing this deduplication
   would cause a concept to appear `verified` or `partial` more easily — but it would also make
   match counts meaningless for any future use of that data.

2. **Deduplication by `result_name` in pass 2 merge.** The pass 2 merge deduplicates by
   `result_name` (not `declaration_id`) when combining pass 1 and pass 2 matches. This is
   intentional: the same declaration may appear in pass 2 under a different context, and keeping
   the first-seen match preserves the original match evidence.

3. **`name_mismatch` is not upgraded by targeted queries.** In `refine_verification()`, the skip
   condition is `status not in {absent, partial}`. A `name_mismatch` entry is passed through
   unchanged. This means targeted queries will not attempt to confirm a name_mismatch. Rationale:
   a name_mismatch already has evidence (it was found in docstrings/informalization). Further
   targeted search is unlikely to find a better name.

4. **Pass 2 returns new responses to the caller — it does not log them.** The caller is
   responsible for calling `log_search_response()` on each returned response. If this contract is
   broken, the `search_log.jsonl` will be incomplete and the audit trail is corrupted.

5. **`extract_concepts()` explicitly skips `candidate_namespaces` and `search_queries`.**
   These are metadata keys in the concepts dict, not hypothesis claims. They must not be added to
   the verifiable concept list.

---

## 8. Things That Must Not Be Broken

- **The match type hierarchy in `_classify_status()`.** The four statuses have specific downstream
  semantics: `absent` triggers gap classification, `partial` lowers the gap confidence calculation
  but still counts toward coverage, `verified` and `name_mismatch` do not trigger additional
  targeted search. Changing priority rules cascades through coverage ratios and gap classification.

- **The `declaration_id` deduplication in pass 1.** Without it, the coverage ratio becomes
  inflated and meaningless.

- **The `VerificationReport.coverage_ratio` property formula.** The formula counts `verified` and
  `partial` as "found" and `absent` as "not found". `name_mismatch` is also counted as "found"
  (it exists, just under a different name). Changing this formula changes the gap threshold
  semantics in `heuristics.py` — the calibrated thresholds (0.3/0.5/0.7) were derived against
  this formula.

- **The `to_dict()` output schema.** The `verification.json` artifact and the combined run report
  both depend on this schema. Changing field names or nesting breaks any downstream tooling that
  reads these files.

- **The `search_fn` async contract in `refine_verification()`.** The function signature is
  `Callable[[str], Any]` but in practice it must be an async callable returning `SearchResponse`.
  The type annotation is too permissive. Do not pass a synchronous function.

---

## 9. Most Dangerous Refactor Mistakes

1. **Removing the `declaration_id` deduplication in `verify_concepts()`.** Coverage ratios would
   inflate silently. A concept like `Finset.sum` would be `verified` against 20 duplicate results
   instead of 1 unique one — but the count would still look like a single entry. No immediate
   error; silent correctness regression.

2. **Changing `_classify_status()` to treat `substring` as `verified`.** Substring matching is
   deliberately `partial` because it catches adjacent declarations, not the exact one. Making it
   `verified` would make nearly every theme appear `well_covered` regardless of actual Mathlib
   content.

3. **Forgetting to log the new `SearchResponse` list returned by `refine_verification()`.** The
   function contract requires the caller to log these. If a future refactor absorbs logging into
   the function itself, it risks double-logging. If it drops logging, the audit trail breaks.

4. **Splitting the module without updating the public `__init__.py` re-exports.** The module is
   currently imported directly from `edge_finder.verification`. If the module is split into
   submodules, `cli.py` and any external consumers must be updated. Missing one import silently
   falls back to an old cached module in some Python environments.

5. **Making the targeted queries concurrent.** `refine_verification()` currently awaits each
   query sequentially. Adding `asyncio.gather()` for concurrency would increase throughput but
   risks LeanExplore rate limiting. If concurrency is added, a semaphore with a limit of ~5
   concurrent requests should be imposed.

6. **Passing `concepts` (original) instead of `concepts_for_verification` (remapped) to pass 2.**
   In `cli.py`, both `verify_concepts()` and `refine_verification()` receive
   `concepts_for_verification` — the remapped version. If a future caller passes the original
   `concepts` dict to pass 2, targeted queries will use un-remapped names, defeating the Iteration
   5 grounding step.

---

## 10. Open Questions and Technical Debt

### Open questions

- **Should `name_mismatch` concepts be refined in pass 2?** Currently they are skipped. An
  argument exists for attempting targeted search using the matched docstring text as a query.
  However, the risk is that the targeted query simply re-confirms the docstring match rather than
  finding the actual declaration name.

- **Is `substring` too generous a criterion for `partial`?** `List.filterMap` matching concept
  `filter` is a false positive at the `partial` level. The list operations run shows 3
  `name_mismatch` entries for `Bool`, `String`, and `Option` — these are single-character or
  short words that match many declaration names by substring. A minimum length guard (e.g., only
  apply substring matching for concepts of 4+ characters) might reduce noise.

- **What happens when `generate_targeted_queries()` produces queries that return 500 errors
  consistently?** The retry logic in `search_single()` handles transient failures. But if a
  particular concept name consistently triggers server errors (as `sum_sigma` did historically),
  the concept will remain `absent` even though it may exist. There is no fallback beyond retry.

### Technical debt

- **No tests.** Zero test coverage for any function in this module. The matching heuristics and
  classification logic are the highest-risk untested code in the pipeline. Priority test cases:
  - `_find_matches()` with edge cases: empty results, concept with dots, short concept names.
  - `_classify_status()` with mixed match types.
  - `generate_targeted_queries()` with qualified concepts, namespace self-prefixing.
  - `refine_verification()` with a mock `search_fn`.

- **No `from_dict()` deserialization.** `VerificationEntry` and `VerificationReport` have
  `to_dict()` but no inverse. This means a run's `verification.json` cannot be reloaded and
  re-processed without re-running the pipeline.

- **`verification/__init__.py` is 468 lines.** Approaching the AGENTS.md 500-line threshold.
  Recommended split:
  - `verification/models.py` — data model classes (`VerificationStatus`, `ConceptKind`,
    `MatchEvidence`, `VerificationEntry`, `VerificationReport`, `extract_concepts`)
  - `verification/matching.py` — matching heuristics (`_normalize`, `_find_matches`,
    `_classify_status`)
  - `verification/passes.py` — public pass functions (`verify_concepts`, `refine_verification`,
    `generate_targeted_queries`)
  - `verification/__init__.py` — re-exports only

- **The `Callable[[str], Any]` type annotation for `search_fn` is too permissive.** It should be
  `Callable[[str], Awaitable[SearchResponse]]`. This requires importing `Awaitable` from `typing`.

- **`coverage_ratio` counts `partial` as "found".** This is debatable — a `partial` match means
  the exact concept was not confirmed. If a future iteration tightens the definition of "covered"
  to `verified` only, the coverage ratios will drop (and the calibrated thresholds in
  `heuristics.py` will need recalibration).
