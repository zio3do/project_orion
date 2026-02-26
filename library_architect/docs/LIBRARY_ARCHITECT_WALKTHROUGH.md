# Library Architect — Walkthrough Document

## 1. What This Subsystem Does

The Library Architect (Pillar 3 of Project Orion) takes a mathematical theme — a named area of mathematics with a companion document describing the scope, gaps, and goals — and produces a **blueprint**: a dependency-ordered plan of Lean 4 definitions and lemmas. Each planned entry includes a complete `LemmaSpec` ready for consumption by the Proof Oracle (Pillar 2). The output is a dual-format artifact: `BLUEPRINT.md` (human-readable) and `blueprint.json` (machine-consumable), plus individual lemma spec files.

The v2 pipeline closes the "grounding loop" — the LLM sees real Mathlib source code and proven oracle exemplars before writing Lean 4 signatures. This eliminated all four categories of signature errors that the v1 pipeline produced.

## 2. Mental Model

Think of the Library Architect as a **research assistant who reads a mathematical survey, studies the existing Mathlib code, and produces a formalization plan grounded in real API usage.** It operates in six stages:

1. **Skeleton Pass** — reads the theme document and generates lightweight names + one-liners. No signatures yet — just the plan structure. This overcomes LLM output length self-limiting.

2. **Skeleton Grounding** — takes each skeleton entry and searches Mathlib via LeanExplore API. Critically, this stage captures `source_text` — the actual Lean 4 source code of related Mathlib declarations. These snippets are the key ingredient for the next stage.

3. **Grounded Expansion** — takes the skeleton + source snippets + oracle exemplars and asks the LLM to produce full Lean 4 signatures. The expansion prompt includes:
   - Mathlib source snippets showing correct typeclass patterns and API usage
   - Oracle test files (`Orion/OracleTests/*.lean`) showing proven correct signatures
   - 10 explicit Lean 4 convention rules addressing every identified error pattern

4. **Re-Grounding** — re-grounds the expanded items against LeanExplore, since the expansion may have changed the search queries.

5. **Assembly** — builds a dependency DAG, validates acyclicity, generates `LemmaSpec` entries, writes output files. Purely algorithmic, no LLM calls.

6. **Elaboration Check** (optional) — wraps each signature in `import Mathlib` + `sorry` body and runs `lake env lean` to verify it elaborates. Batched mode puts all signatures in one file (one Mathlib import cost instead of N).

```
Theme doc (markdown)
        │
        ▼
┌──────────────────┐
│   Skeleton Pass  │  ← LLM (GPT-4o): names + one-liners + deps
│   (Stage 1)      │     Output: skeleton JSON
└──────┬───────────┘
       │
       ▼
┌──────────────────┐
│   Skeleton       │  ← LeanExplore API: search, collect source_text
│   Grounding      │     Output: GroundedDecomposition with source_snippets
│   (Stage 2)      │
└──────┬───────────┘
       │ Mathlib source snippets
       ▼
┌──────────────────┐
│   Grounded       │  ← LLM (GPT-4o): expand with source context
│   Expansion      │     + oracle exemplars + convention rules
│   (Stage 3)      │     Output: Decomposition (grounded signatures)
└──────┬───────────┘
       │
       ▼
┌──────────────────┐
│   Re-Grounding   │  ← LeanExplore API: re-classify expanded items
│   (Stage 4)      │     Output: GroundedDecomposition (final)
└──────┬───────────┘
       │
       ▼
┌──────────────────┐
│   Assembly       │  ← Algorithm: DAG sort + LemmaSpec + files
│   (Stage 5)      │
└──────┬───────────┘
       │
       ▼ (optional)
┌──────────────────┐
│   Elaboration    │  ← lake env lean: sorry-check all signatures
│   Checker        │     Output: elaboration_report.json
│   (Stage 6)      │
└──────────────────┘
```

## 3. Directory Structure

```
library_architect/
├── __init__.py              # Package marker with module docstring
├── __main__.py              # Entry point: loads .env, calls cli.main()
├── cli.py                   # CLI orchestrator: argument parsing, stage sequencing
│                            #   Two modes: default (grounded) and --legacy
├── config.py                # Constants: output dirs, model names, metadata
├── models.py                # All data models (frozen dataclasses with JSON round-trip)
├── decomposer.py            # LLM decomposition: skeleton_pass(), expand_with_grounding()
│                            #   Also: _find_oracle_exemplars(), _collect_grounding_context()
├── grounder.py              # LeanExplore grounding: ground(), ground_skeleton()
│                            #   Captures source_text, builds source_snippets
├── assembler.py             # DAG validation + blueprint generation
├── elaboration_checker.py   # Sorry-elaboration quality gate
│                            #   Batched (default) or sequential checking
├── prompts/
│   ├── decomposer_prompt.md           # (legacy) single-pass prompt
│   ├── decomposer_skeleton_prompt.md  # Pass 1: skeleton generation prompt
│   └── decomposer_expand_prompt.md    # Pass 2: grounded expansion prompt
│                                      #   10 convention rules, source context injection
├── themes/
│   └── graded_order_combinatorics.md  # Test theme document
├── docs/
│   ├── library_architect_design.md    # Design document
│   └── LIBRARY_ARCHITECT_WALKTHROUGH.md  # This file
├── .cache/                  # Disk cache (not version controlled)
│   ├── decomposition/       # Cached skeleton + expansion LLM responses
│   └── grounding/           # Cached LeanExplore search results
└── runs/                    # Generated output
    └── graded_order_combinatorics/
        ├── BLUEPRINT.md
        ├── blueprint.json
        ├── elaboration_report.json
        └── lemma_specs/
            ├── level.json
            ├── rankGenPoly.json
            └── ...
```

## 4. Call Graph

```
__main__.py
  └── cli.main(argv)
        ├── config.build_metadata()
        ├── [--clear-cache] → shutil.rmtree(.cache/)
        │
        ├── [default mode: _run_grounded_pipeline()]
        │     │
        │     ├── decomposer.skeleton_pass(theme, theme_doc, model, use_cache)
        │     │     ├── _load_prompt("decomposer_skeleton_prompt.md")
        │     │     ├── _build_skeleton_prompt(theme, theme_doc)
        │     │     ├── [cache check] _load_cached(key)
        │     │     ├── LlmClient(model).complete_json()
        │     │     └── [cache save] _save_to_cache(key, data)
        │     │
        │     ├── grounder.ground_skeleton(skeleton, theme, use_cache)
        │     │     └── asyncio.run(_ground_all_skeleton(...))
        │     │           └── for each definition/lemma:
        │     │                 ├── _skeleton_search_queries(name, informal)
        │     │                 ├── _ground_single(name, queries, ...)
        │     │                 │     [collects source_text per result]
        │     │                 └── _classify(name, responses)
        │     │                       → GroundingResult with source_snippets
        │     │
        │     ├── decomposer.expand_with_grounding(theme, skeleton, theme_doc,
        │     │         grounded, model, use_cache)
        │     │     ├── _find_oracle_exemplars()
        │     │     │     [scans Orion/OracleTests/*.lean]
        │     │     ├── _collect_grounding_context(grounded)
        │     │     │     [extracts source_snippets per item]
        │     │     ├── _load_prompt("decomposer_expand_prompt.md")
        │     │     ├── [split items into batches of 6]
        │     │     └── for each batch:
        │     │           ├── _build_expansion_prompt(theme, theme_doc, skeleton,
        │     │           │         batch, grounding_context, oracle_exemplars)
        │     │           ├── LlmClient.complete_json() (up to 3 retries)
        │     │           └── [cache save]
        │     │
        │     ├── grounder.ground(decomposition, use_cache)
        │     │     [re-ground with expanded search queries]
        │     │
        │     ├── assembler.assemble(grounded, output_dir, theme_doc_path)
        │     │     ├── _topological_sort(dag, all_names)
        │     │     ├── _build_entry(...)
        │     │     ├── _generate_blueprint_md(blueprint)
        │     │     └── file I/O
        │     │
        │     └── [--check-signatures] → _run_elaboration_check(blueprint)
        │           └── elaboration_checker.check_blueprint(entries)
        │                 ├── _generate_batched_lean_file(entries)
        │                 ├── subprocess: lake env lean <batch.lean>
        │                 ├── _parse_batched_errors(stderr, entry_ranges)
        │                 └── → ElaborationReport
        │
        └── [--legacy: _run_legacy_pipeline()]
              ├── decomposer.decompose(theme, theme_doc, model, use_cache)
              ├── grounder.ground(decomposition, use_cache)
              ├── assembler.assemble(grounded, output_dir, theme_doc_path)
              └── [--check-signatures] → _run_elaboration_check(blueprint)
```

## 5. Execution Lifecycle

### Full pipeline (v2 grounded mode)

```
python -m library_architect "Graded Order Combinatorics" \
    --theme-doc library_architect/themes/graded_order_combinatorics.md \
    --output-dir library_architect/runs/graded_order_combinatorics \
    --check-signatures
```

1. **Bootstrap**: `__main__.py` loads `.env` via `python-dotenv`, then calls `cli.main()`.

2. **Argument parsing**: CLI parses theme name, optional theme doc path, output directory, model override, `--skip-grounding`, `--no-cache`, `--clear-cache`, `--legacy`, and `--check-signatures` flags.

3. **Stage 1 — Skeleton Pass** (~5s):
   - Loads `prompts/decomposer_skeleton_prompt.md`.
   - Asks the LLM for a lightweight plan: names, one-sentence descriptions, layer assignments, dependencies.
   - The skeleton prompt requires 15-25 lemmas. Each entry is ~100-150 chars, so the LLM produces the full plan without output length limits.
   - If the theme document has a "Promoted Lemmas" table, the skeleton prompt requires these appear (rule 5).
   - Cached by SHA-256 of (theme + theme_doc + model).

4. **Stage 2 — Skeleton Grounding** (~10-30s):
   - Uses `ground_skeleton()` which generates search queries from skeleton names + informals.
   - Searches LeanExplore for each entry.
   - **Key v2 feature:** Captures `source_text` from each search result and stores it in `GroundingResult.source_snippets`.
   - These source snippets are the grounding signal for the expansion prompt.
   - Example: searching for "GradeOrder" returns the actual source code of `Mathlib.Order.Grade`, showing the correct typeclass chain `[Preorder α] [GradeOrder ℕ α]`.

5. **Stage 3 — Grounded Expansion** (~10-20s):
   - Splits skeleton items into batches of 6.
   - For each batch, builds an expansion prompt that includes:
     - The full skeleton for cross-referencing context
     - **Mathlib source snippets** from skeleton grounding (per-item context sections)
     - **Oracle exemplar files** from `Orion/OracleTests/*.lean`
     - **10 convention rules** covering typeclass chains, universe-polymorphic variables, `noncomputable`, `GradeMinOrder` vs `GradeOrder`, etc.
   - Each batch call includes retry logic (up to 3 attempts).
   - Each batch is independently cached.

6. **Stage 4 — Re-Grounding** (~10-30s):
   - Re-grounds the expanded decomposition using the new search queries from expansion.
   - Classification may change (e.g., a previously `novel` entry may now be `partial_overlap` with better search queries).

7. **Stage 5 — Assembly** (~instant):
   - Builds dependency DAG, runs Kahn's topological sort.
   - Generates `BlueprintEntry` + `LemmaSpec` for each planned item.
   - Writes `BLUEPRINT.md`, `blueprint.json`, and individual `lemma_specs/<name>.json`.

8. **Stage 6 — Elaboration Check** (optional, ~3-5 min):
   - Generates a single `.lean` file containing all signatures, each in its own `section` block.
   - Runs `lake env lean` once (batched mode amortizes the ~3-4 min Mathlib import).
   - Parses errors from stderr and attributes them to individual signatures by line number.
   - Writes `elaboration_report.json` to the output directory.

9. **Output**: CLI prints summary statistics and file paths.

### CLI flags

| Flag | Effect |
|------|--------|
| `--check-signatures` | Run elaboration check after assembly (requires lake). |
| `--legacy` | Use v1 pipeline (expansion before grounding, no source context). |
| `--skip-grounding` | Bypass grounding stages. All entries get `ungrounded` status. |
| `--no-cache` | Disable disk cache for both decomposition and grounding. |
| `--clear-cache` | Delete the entire `.cache/` directory before running. |
| `--model MODEL` | Override the LLM model (default: `gpt-4o`). |

## 6. Key Function Annotations

### `decomposer.skeleton_pass()` (decomposer.py)

Entry point for Stage 1. Generates a lightweight skeleton with names, one-line descriptions, layer assignments, and dependency links. Cache-keyed by SHA-256 of (theme + theme_doc + model). The skeleton prompt enforces promoted lemmas from the theme document.

### `decomposer.expand_with_grounding()` (decomposer.py)

Entry point for Stage 3. Takes skeleton + grounding results and produces full `Decomposition` with Lean 4 signatures. The function:
1. Calls `_find_oracle_exemplars()` to locate `Orion/OracleTests/*.lean` files
2. Calls `_collect_grounding_context()` to extract source snippets per skeleton item
3. Splits items into batches of 6 and builds per-batch expansion prompts
4. Each prompt includes: skeleton context + source snippets + oracle exemplars + convention rules

### `decomposer._find_oracle_exemplars()` (decomposer.py)

Scans the `Orion/OracleTests/` directory for `.lean` files. Returns a list of `(filename, content)` tuples. These files contain proven Lean 4 code that demonstrates correct patterns (typeclass assumptions, API usage, `noncomputable` placement). Injected into the expansion prompt as few-shot exemplars.

### `decomposer._collect_grounding_context()` (decomposer.py)

Extracts `source_snippets` from a `GroundedDecomposition`, organizing them by item name. Returns a dict mapping item names to their Mathlib source context strings. Each context string shows the actual source code of related Mathlib declarations.

### `grounder.ground_skeleton()` (grounder.py)

Stage 2 entry point. Takes skeleton JSON (not a `Decomposition` object) and grounds each entry against LeanExplore. Uses `_skeleton_search_queries()` to generate queries from just names and informals (since no full signatures exist yet). The key feature is `source_text` capture — each `SearchResult` carries the actual Lean 4 source code of the matched declaration.

### `grounder._classify()` (grounder.py)

The core grounding heuristic. Uses case-insensitive, punctuation-stripped name matching. Collects `source_snippets` from all search results that have non-empty `source_text`. The matching rule `name_lower in rname_lower or rname_lower.endswith(name_lower)` is intentionally loose — better to flag false positives for human review.

### `elaboration_checker._generate_batched_lean_file()` (elaboration_checker.py)

Generates a single `.lean` file containing all signatures, each in its own `section`/`end` block with a unique `-- @@ELAB_CHECK: <name>` marker comment. This allows attributing errors from stderr back to individual signatures by line number range. Uses `open Finset` and `open Polynomial` (without `in`) for file-wide scope.

### `elaboration_checker._parse_batched_errors()` (elaboration_checker.py)

Parses Lean's stderr output (format: `filename:line:col: error: message`) and uses the line number to attribute each error to the correct entry's line range. Returns a dict mapping entry names to their error lines.

### `assembler._topological_sort()` (assembler.py)

Kahn's algorithm for topological sorting. The DAG is filtered to only include internal names. Raises `ValueError` with cycle members if a cycle is detected.

## 7. Critical Invariants

1. **Dependency DAG must be acyclic.** The assembler validates this and crashes (with a clear error) if violated.

2. **All names in the blueprint are unique.** Duplicate names cause silent overwrites in the assembler's dictionary lookup.

3. **LemmaSpec schema compatibility.** Must match `proof_oracle.runner.orchestrator.run_lemma()`.

4. **Grounding is advisory, not authoritative.** The `exists` classification is heuristic — human review of BLUEPRINT.md is mandatory.

5. **LLM output is non-deterministic.** The same theme document produces different decompositions on each run.

6. **Cache invalidation is manual.** Use `--clear-cache` to reset.

7. **The expansion prompt must receive source_snippets when grounding is available.** This is the core mechanism that produces correct signatures.

8. **Elaboration checking must not modify signatures.** It reports pass/fail only.

## 8. Things That Must Not Be Broken

1. **The `LemmaSpec` output format.** The Proof Oracle depends on this schema.

2. **The topological sort's cycle detection.** Removing this allows broken dependency ordering.

3. **The `.env` loading in `__main__.py`.** Without it, API keys are unavailable.

4. **The `edge_finder.llm.client` import via `sys.path` manipulation.** Fragile coupling — if `edge_finder/` moves, the decomposer breaks.

5. **The LeanExplore API endpoint URL.** `https://www.leanexplore.com/api/v2/search` with query parameter `q`.

6. **The two-pass decomposition structure.** Skeleton (15-25 items lightweight) + expansion (batches of 6 with context). Collapsing to single-pass reintroduces the output length self-limiting problem.

7. **Grounder inter-request spacing.** 100ms delay prevents rate limiting.

8. **Source text capture in grounder.** The `SearchResult.source_text` field and `GroundingResult.source_snippets` are the grounding loop's data channel. Removing these breaks the entire v2 value proposition.

9. **Oracle exemplar discovery.** `_find_oracle_exemplars()` scans `Orion/OracleTests/`. If the directory moves, exemplar injection stops silently (the expansion prompt degrades but doesn't fail).

10. **Batched elaboration line attribution.** The `-- @@ELAB_CHECK: <name>` markers and `section`/`end` blocks allow attributing errors to specific signatures. Changing the format breaks error parsing.

## 9. Most Dangerous Refactor Mistakes

1. **Collapsing back to single-pass decomposition.** Reintroduces the LLM output length self-limiting problem.

2. **Removing skeleton grounding or source_text capture.** This is the core v2 improvement. Without it, the expansion prompt generates signatures from LLM memory, producing the four error categories.

3. **Removing oracle exemplar injection.** The exemplars are the strongest grounding signal for correct typeclass patterns and API usage. Without them, the convention rules alone may not prevent all errors.

4. **Changing the expansion batch size from 6.** Larger batches risk output truncation. Smaller batches are slower and more expensive.

5. **Parallelizing grounder queries with `asyncio.gather`.** Speed improvement but risks rate-limiting by LeanExplore API.

6. **Moving `open Finset`/`open Polynomial` to `open ... in` in batched elaboration.** The `in` keyword scopes to the next expression only, so subsequent declarations would lose the open scope.

7. **Reducing elaboration timeout below 300s.** Mathlib import takes ~3-4 min on typical hardware. A 90s timeout causes false negatives.

8. **Modifying `_classify()` to require exact name matching.** The current loose matching (`name_lower in rname_lower`) intentionally catches partial matches for human review.

## 10. Open Questions and Technical Debt

### Open Questions

1. **Should grounding use LLM-assisted classification?** The current heuristic produces many `partial_overlap` results. An LLM could review search results for more precise classification, at additional cost.

2. **Optimal expansion batch size?** Currently 6. Needs empirical tuning across different themes.

3. **How to handle themes without oracle exemplars?** Convention rules + source snippets provide grounding, but exemplars are the strongest signal. Should we generate synthetic exemplars?

4. **Should failed elaboration signatures be auto-repaired?** Currently the checker reports but doesn't fix. An LLM repair loop could iterate on failed signatures using the error messages.

### Technical Debt

1. **`sys.path` hack for `edge_finder` import** (decomposer.py). Should be replaced with proper package installation.

2. **No input validation on LLM response beyond JSON parsing.** Should add schema validation.

3. **No test suite.** Key testable units: `_classify`, `_topological_sort`, `_generate_batched_lean_file`, `_parse_batched_errors`, JSON round-tripping of all models.

4. **`runs/` directory accumulates stale lemma spec files.** The assembler doesn't clean up specs from previous runs. *(Partially addressed in v2.1: manual cleanup performed for graded_order_combinatorics. The assembler should be updated to clean stale specs automatically.)*

5. **Legacy `decomposer_prompt.md` still exists.** No longer used but kept for reference.

### Resolved Issues

- ~~Signatures generated from LLM memory~~ → v2 grounding loop injects Mathlib source text + oracle exemplars
- ~~18-minute elaboration time (sequential, 20+ sigs)~~ → Batched mode: one Mathlib import, ~3-4 min total
- ~~90s timeout too short~~ → Increased to 300s
- ~~No caching~~ → Disk caching for decomposition and grounding
- ~~Blueprint count depends on LLM mood (5-8)~~ → Two-pass decomposition produces 15-20 consistently
- ~~No retry on 429~~ → Exponential backoff on 5xx and 429
- ~~`source_text` discarded by grounder~~ → Captured in `SearchResult`, carried in `GroundingResult.source_snippets`
- ~~`level_monotonicity` likely mathematically false~~ → Confirmed false and removed in v2.1 correction pass. |level_k| ≤ |level_{k+1}| does not hold for general graded posets.
- ~~Stale lemma specs accumulate in `runs/`~~ → Cleaned up for graded_order_combinatorics in v2.1 (39 → 12 files), expanded to 18 files in v2.2

## 11. Results

### v2.0 (automated pipeline output)

The v2 pipeline on the `graded_order_combinatorics` theme:

| Metric | Value |
|--------|-------|
| Total entries | 19 (3 definitions + 16 lemmas) |
| Planned | 18 |
| Exists in Mathlib | 1 (`level` → `Erdos1043.levelSet`) |
| Elaboration pass rate | **18/18 (100%)** |
| Oracle signature matches | **3/3 exact** |
| Pipeline duration | ~60s (excluding elaboration) |
| Elaboration duration | ~3-4 min (batched, one Mathlib import) |
| LLM cost | ~$0.10 |

### v2.1 (after manual correction pass)

Manual audit revealed 7 entries with errors that the elaboration checker cannot detect
(mathematically false statements, semantic redundancy, malformed hypotheses, placeholder
entries). After correction:

| Metric | Value |
|--------|-------|
| Total entries | 13 (2 definitions + 11 lemmas) |
| Planned | 12 |
| Exists in Mathlib | 1 (`level`) |
| Entries removed | 7 (see `blueprint.json` `removed_entries`) |
| Entries added | 1 (`saturatedChain_length_const`) |
| Entries renamed | 1 (`rankGenPoly_degree` → `rankGenPoly_natDegree`) |
| Elaboration pass rate | **13/13 (100%)** |
| Oracle signature matches | **3/3 exact** |
| Elaboration file | `Orion/ElabCheck/BlueprintV21.lean` |

**Key lesson:** Elaboration checking catches syntax/typeclass errors but not mathematical
incorrectness or semantic issues. Manual audit is essential. The `removed_entries` section
in `blueprint.json` documents each removal with the specific reason.

### v2.2 (extensions)

6 natural extensions added to restore the blueprint to 19 entries with correct, audited content.
No Mathlib overlap found for any extension (verified via LeanExplore).

| Metric | Value |
|--------|-------|
| Total entries | 19 (2 definitions + 17 lemmas) |
| Planned | 18 |
| Exists in Mathlib | 1 (`level`) |
| Entries added | 6 (see below) |
| Elaboration pass rate | **19/19 (100%)** |
| Oracle signature matches | **3/3 exact** (unchanged) |
| Elaboration file | `Orion/ElabCheck/BlueprintV22.lean` |
| Lemma spec files | 18 (12 from v2.1 + 6 new) |

New entries in v2.2:
- `rankGenPoly_eval_zero` (Layer 2, easy) — eval at 0 = |level 0|
- `rankGenPoly_coeff_eq_zero` (Layer 2, easy) — empty level → zero coefficient
- `grade_le_of_chain` (Layer 3, easy) — ℕ subtraction guard
- `saturatedChain_length_grade_diff` (Layer 3, easy) — length = grade diff + 1
- `saturatedChain_grade_strictMono` (Layer 3, easy) — grades strictly increase
- `saturatedChain_nodup` (Layer 3, easy) — element distinctness

### Oracle Signature Comparison (unchanged through v2.1 and v2.2)

| Lemma | Generated vs Oracle | Key Matches |
|-------|-------------------|-------------|
| `levelCard_sum` | Exact match | `[Preorder α]`, `(Finset.univ : Finset α).image (grade ℕ)`, `Fintype.card α` |
| `rankGenPoly` (def) | Match (modulo `level` abbrev) | `noncomputable`, `Polynomial ℕ`, `.card • (Polynomial.X ^ k)` |
| `rankGenPoly_eval_one` | Exact match | `Polynomial.eval 1`, explicit `(α : Type*)` |
| `saturatedChain_length` | Exact match | `[GradeMinOrder ℕ α]` (not `GradeOrder`), `l.Chain' (· ⋖ ·)`, `l.getLast hne` |
