# Proof Oracle — Ownership Transfer Walkthrough

## 1. What This Subsystem Does

The Proof Oracle is a Python orchestrator that takes a single lemma specification (name, informal statement, Lean 4 signature, dependencies) and produces a verified Lean 4 proof. It first runs a **pre-search step** (cheap LLM call + LeanExplore API) to find relevant Mathlib context, then spawns Claude Code CLI sessions equipped with MCP tools (lean-lsp-mcp for Lean diagnostics, LeanExplore for Mathlib search), parses the agent's output, and runs a hard verification gate (`lake env lean` + sorry/axiom scanning). If verification fails, it retries with error context up to a configurable budget. The Proof Oracle knows nothing about pockets, dependencies between lemmas, or Mathlib contribution strategy — it proves one lemma at a time.

## 2. Mental Model

Think of the Proof Oracle as a **factory with an inspector**.

```
                    ┌──────────────────────────────────┐
  lemma_spec.json → │  Python Orchestrator (dumb)       │ → verified .lean file
                    │                                    │   + MANIFEST.md
                    │  ┌──────────┐                     │
                    │  │Pre-Search│ (Sonnet + LeanExplore)
                    │  └────┬─────┘                     │
                    │       ↓ context                    │
                    │  ┌─────────────┐  ┌────────┐     │
                    │  │ Claude Code  │→ │Verifier│     │
                    │  │ (smart, but  │  │(trusted│     │
                    │  │  untrusted)  │  │  gate) │     │
                    │  └─────────────┘  └────────┘     │
                    │       ↕ MCP            ↑          │
                    │  lean-lsp  lean-explore │          │
                    │                  lake env lean     │
                    └──────────────────────────────────┘
```

**The orchestrator is dumb.** It does no reasoning — it reads files, spawns subprocesses, checks return values, and writes status updates. All intelligence lives in the Claude Code agent session.

**The verifier is the bouncer.** The agent's self-report (`END_REASON:COMPLETE`) is logged but never trusted. Only `lake env lean` returning zero errors + no sorry + no axiom constitutes a pass. This is the single most important invariant.

**Each attempt is a fresh session.** The orchestrator does not continue a failed Claude Code session — it starts a new one with error context from the previous attempt. This prevents context pollution from failed proof searches filling the window.

The data flow is a loop with a pre-search warmup:

```
spec → pre_search(Sonnet + LeanExplore) → Mathlib context
                                               ↓
     → build_prompt(spec + context) → claude -p → parse END_REASON
                                                       ↓
                                              verify(target_file)
                                                  ↓          ↓
                                              PASS → done    FAIL → retry (with error context)
```

## 3. Directory Structure

```
proof_oracle/
├── __init__.py                    # Package docstring
├── docs/
│   ├── proof_oracle_design.md     # APPROVED design doc (829 lines)
│   └── proof_oracle_walkthrough.md  # This file
├── lemma_specs/                   # Input: one JSON per lemma
│   ├── fwdDiff_linear.json        # Phase 1 target (easy, proved)
│   ├── div_mod_unique.json        # Test: Euclidean division uniqueness (medium, proved)
│   ├── sum_range_id.json          # Test: Gauss sum formula (medium, proved)
│   └── fwdDiff_mul.json           # Novelty test: discrete product rule (medium, proved)
├── prompts/                       # Prompt templates (read-only at runtime)
│   ├── system_prompt.md           # Agent identity, tool discipline, sorry-not-axiom
│   └── task_template.md           # Step-by-step workflow (setup → prove → verify)
├── runner/                        # The orchestration engine
│   ├── __init__.py                # Package docstring
│   ├── orchestrator.py            # Top-level entry point + proof loop
│   ├── pre_search.py              # Pre-search: Sonnet query gen + LeanExplore search
│   ├── prompt_builder.py          # Assembles prompt from templates + spec + context
│   ├── session.py                 # Claude Code subprocess manager (with cost parsing)
│   ├── verifier.py                # Hard verification gate (lake env lean)
│   └── manifest.py                # MANIFEST.md reader/writer (with cost tracking)
└── runs/                          # Output: one dir per run (gitignored)
    └── <lemma>_<timestamp>/
        ├── MANIFEST.md            # Status, attempts, cost, notes
        └── session_logs/
            └── attempt_NN_*.json  # Full prompt + stdout + stderr + cost per attempt
```

**Key files outside `proof_oracle/`:**

- `.mcp.json` — MCP server registrations for Claude Code (gitignored, contains API key)
- `.env` — API keys: `CLAUDE_API_KEY`, `LEANEXPLORE_API_KEY` (gitignored)
- `Orion/` — Lean source files that the agent reads and writes

## 4. Call Graph

```
main()                                  # orchestrator.py:254
  └─ run_lemma(spec_path)               # orchestrator.py:71
       ├─ _load_lemma_spec(path)        # orchestrator.py:42  → LemmaSpec
       ├─ Manifest.load(path)           # manifest.py
       ├─ run_pre_search(...)           # pre_search.py:319  → PreSearchResult
       │    ├─ _get_api_keys(root)      # loads .env for Anthropic + LeanExplore keys
       │    ├─ _generate_queries(...)   # Sonnet call → 3-5 search queries
       │    ├─ _search_leanexplore(...) # API calls → deduplicated declarations (max 15)
       │    └─ _format_context_block()  # markdown for prompt injection
       └─ [loop: attempt 1..budget]
            ├─ build_prompt(spec, pre_search_context, ...)  # prompt_builder.py:67
            │    ├─ _load_template("system_prompt.md")
            │    ├─ _load_template("task_template.md")
            │    └─ assemble sections (task header, spec, deps, Mathlib context, errors)
            ├─ run_session(prompt, ...)  # session.py:163
            │    ├─ _build_env(root)     # session.py:134  → loads .env, maps API keys
            │    ├─ subprocess.run(["claude", "-p", prompt, ...])
            │    ├─ _parse_end_reason()  # session.py:68   → COMPLETE|LIMIT|ERROR|UNKNOWN
            │    ├─ _parse_cost()        # session.py:99   → total_cost_usd from JSON
            │    └─ _save_session_log()  # session.py:113  → JSON to runs/
            ├─ verify(lean_file, root)   # verifier.py:145
            │    ├─ subprocess.run(["lake", "env", "lean", file])
            │    ├─ _parse_lean_errors(combined_output)
            │    ├─ _check_sorry_in_output(combined_output)
            │    └─ _scan_for_axiom_declarations(file)
            └─ manifest.upsert_entry() + manifest.write()  # includes accumulated cost
```

## 5. Execution Lifecycle Walkthrough

**Running the pipeline:**

```bash
source .env && export ANTHROPIC_API_KEY="${CLAUDE_API_KEY}"
conda run -n proof_oracle python -m proof_oracle.runner.orchestrator \
  proof_oracle/lemma_specs/div_mod_unique.json
```

**What happens step by step:**

1. **Load spec.** `_load_lemma_spec` reads the JSON, validates required fields, returns a `LemmaSpec` dataclass. If any field is missing, it raises `ValueError` immediately.

2. **Create run directory.** A unique run ID is generated from the lemma name + UTC timestamp (e.g., `div_mod_unique_20260222T105928Z`). Session logs and MANIFEST.md go here.

3. **Initialize MANIFEST.** The manifest tracks status (`in_progress` → `done`/`failed`), attempt count, accumulated cost, and error notes. It's written after every attempt so that progress survives crashes.

4. **Pre-search.** Before the proof loop, `run_pre_search()` does two things:
   - Calls Claude Sonnet 4 (via httpx, ~$0.002) to generate 3-5 semantic search queries from the lemma spec.
   - Runs each query against the LeanExplore API, deduplicates results, and caps at 15 declarations.
   - Formats the results as markdown (~4-5K tokens) for prompt injection.

   This step is non-fatal — if it fails, the orchestrator continues without context. The pre-search context is injected into every attempt's prompt under "Relevant Mathlib Context (Pre-Searched)."

5. **Build prompt.** `build_prompt` concatenates: system prompt (agent identity, tool discipline, sorry-not-axiom policy, END_REASON protocol) + task template (step-by-step workflow) + task-specific section (lemma spec, dependencies, pre-search Mathlib context, retry error context). The prompt is ~8-10K characters for first attempts (larger with pre-search context), bigger on retries due to error context.

6. **Spawn Claude Code.** `run_session` calls `claude -p <prompt> --output-format json --permission-mode bypassPermissions`. It sets `cwd` to the project root (so `.mcp.json` is found and the agent can read/write Lean files), and injects API keys from `.env` into the subprocess environment. Timeout is 15 minutes.

7. **Agent works.** Inside the Claude Code session, the agent:
   - Reads the target Lean file
   - Writes the theorem statement (initially with `sorry`)
   - Checks diagnostics via lean-lsp-mcp
   - Searches Mathlib via LeanExplore if needed
   - Iterates on the proof, checking diagnostics after each change
   - Reports `END_REASON:COMPLETE`, `LIMIT`, or `ERROR`

8. **Parse result.** `_parse_end_reason` extracts the sentinel from the JSON output. `_parse_cost` extracts `total_cost_usd` from the same JSON. The Claude Code JSON envelope has `{"type":"result","result":"<agent text>","total_cost_usd":...}` — we parse the `result` field for END_REASON and the top-level `total_cost_usd` for cost. The agent sometimes wraps the sentinel in backticks (`\`END_REASON:COMPLETE\``), which the regex handles.

9. **Verification gate.** `verify()` runs `lake env lean <file>` and checks:
   - Zero compiler errors (parsed from combined stdout+stderr)
   - No sorry warnings (checked with multiple quote formats)
   - No axiom declarations in source (regex scan with comment awareness)

   If all three pass → the proof is accepted. If any fail → the error details become retry context.

10. **Retry or finish.** On failure, `previous_errors` is set to the verification summary + raw compiler output. The next iteration's prompt includes this under "Previous Attempt Errors." On success or budget exhaustion, the MANIFEST is updated (including accumulated cost) and the function returns.

## 6. Annotated Excerpts of Key Functions

### The verification gate (verifier.py:145)

This is the most security-critical function. It must never return `passed=True` for an unsound proof.

```python
def verify(lean_file, project_root, timeout=600):
    # Step 1: Run the compiler. This is the ground truth.
    result = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=str(project_root),
        capture_output=True, text=True, timeout=timeout,
    )

    # Step 2: Combine stdout+stderr. Lean routes different diagnostics
    # to different streams — we learned this the hard way.
    combined_output = result.stdout + "\n" + result.stderr

    # Step 3: Three independent checks. ALL must pass.
    errors = _parse_lean_errors(combined_output)      # zero errors?
    has_sorry = _check_sorry_in_output(combined_output) # no sorry?
    has_axiom = _scan_for_axiom_declarations(file)     # no axiom?

    passed = len(errors) == 0 and not has_sorry and not has_axiom
```

The sorry check handles multiple quote formats (backticks, single quotes, unicode quotes) because Lean's output format varies. The axiom scanner uses a regex with awareness of line comments and block comments to avoid false positives.

### The session manager (session.py:163)

The critical detail is `--permission-mode bypassPermissions`, which allows the agent to use MCP tools without interactive permission prompts.

```python
cmd = [
    "claude", "-p", prompt,
    "--output-format", "json",
    "--permission-mode", "bypassPermissions",
]
env = _build_env(project_root)  # loads .env, maps CLAUDE_API_KEY → ANTHROPIC_API_KEY

result = subprocess.run(
    cmd, cwd=str(project_root),   # cwd is project root so .mcp.json is found
    capture_output=True, text=True,
    timeout=timeout, env=env,
)
```

### The proof loop with pre-search (orchestrator.py:133)

The orchestrator runs pre-search once, then loops attempts with that context:

```python
# Pre-search: runs once per lemma
pre_search_result = run_pre_search(
    lemma_name=spec.lemma_name,
    informal_statement=spec.informal_statement,
    suggested_signature=spec.suggested_signature,
    depends_on=spec.depends_on,
    project_root=project_root,
)
pre_search_context = pre_search_result.context_block
entry.cost_usd += pre_search_result.cost_usd

for attempt in range(1, spec.attempt_budget + 1):
    prompt = build_prompt(spec, ..., pre_search_context=pre_search_context,
                          previous_errors=previous_errors, attempt_number=attempt)
    session_result = run_session(prompt, project_root, ...)
    entry.cost_usd += session_result.cost_usd  # accumulate cost

    verification = verify(lean_file, project_root)
    if verification.passed:
        entry.status = "done"
        return True

    # Failed — set up retry context
    previous_errors = f"Verification result: {verification.summary()}\n..."
```

## 7. Critical Invariants

1. **The verifier is the single source of truth.** `lake env lean` returning clean output is the ONLY way a proof is accepted. The agent's `END_REASON:COMPLETE` is informational logging, not a gate.

2. **sorry-not-axiom policy.** `axiom` declarations are forbidden because they silently introduce unsoundness (the file compiles but mathematical guarantees are broken). `sorry` is permitted because it produces a compiler warning that the verifier catches. This asymmetry is deliberate and non-negotiable.

3. **Fresh session per attempt.** Each retry spawns a new Claude Code process. The orchestrator never uses `--continue` or `--resume`. This prevents context pollution from failed proof search filling the window.

4. **The orchestrator does no reasoning.** It reads files, spawns processes, checks return codes, and writes logs. All intelligence is in the prompt templates and the Claude Code agent. If you find yourself adding conditional logic based on proof content to the orchestrator, stop — that logic belongs in the prompt.

5. **MANIFEST is written after every attempt.** If the process crashes mid-run, the MANIFEST reflects the last completed attempt. Session logs are saved before verification so that even if verification crashes, the agent's output is preserved.

6. **Combined stdout+stderr for Lean output.** Lean routes sorry warnings to stdout and errors to stderr (or vice versa depending on version). The verifier always checks the combined stream.

## 8. Things That Must Not Be Broken

1. **The three-check conjunction in `verify()`.** The pass condition is `errors == 0 AND no sorry AND no axiom`. If any check is removed or weakened, unsound proofs can slip through.

2. **The sorry check's quote-format coverage.** Lean uses backticks (`` `sorry` ``), but future versions might change this. The check must handle all reasonable formats.

3. **`cwd=project_root` in both `run_session` and `verify`.** Claude Code needs `cwd` set to find `.mcp.json`. The verifier needs `cwd` set so `lake` resolves the lakefile. Changing either breaks the pipeline silently.

4. **`--permission-mode bypassPermissions` in the claude command.** Without this, the agent cannot use MCP tools or file operations in non-interactive (`-p`) mode, and the session hangs or fails silently.

5. **The `.env` → `ANTHROPIC_API_KEY` mapping.** The `.env` stores `CLAUDE_API_KEY`, but the Claude CLI reads `ANTHROPIC_API_KEY`. `_build_env` does the mapping. If this breaks, sessions fail with auth errors.

6. **`.mcp.json` at project root.** This file contains MCP server registrations (and the LeanExplore API key in args). It must be gitignored. If it's missing, Claude Code has no MCP tools and produces garbage proofs that fail verification.

## 9. Most Dangerous Refactor Mistakes

1. **Trusting the agent's END_REASON instead of the verifier.** If someone short-circuits the loop with `if session_result.agent_believes_complete: return True`, unsound proofs will be accepted. The verifier must always run.

2. **Adding `--continue` to retry sessions.** Continuing a Claude Code session seems efficient but fills the context window with failed proof attempts, making the agent less effective. Fresh sessions with curated error context outperform continuation.

3. **Moving MCP server registration to user scope.** The MCP config is at project scope (`.mcp.json`) so it's tied to this Lean project's directory. User-scope registration would break when running from a different project.

4. **Removing the axiom scan.** The axiom scan is the only defense against silent unsoundness. `lake env lean` does NOT flag axiom declarations — the file compiles cleanly with axioms. Only the source-level scan catches this.

5. **Hardcoding paths to conda env binaries.** The MCP server paths in `.mcp.json` point to `/opt/homebrew/Caskroom/miniforge/base/envs/proof_oracle/bin/...`. If the conda env moves or is recreated, these paths break. A future improvement would resolve these dynamically.

6. **Parallelizing the proof loop.** The loop writes to the same target `.lean` file. If two attempts run concurrently, they'll clobber each other's writes. Parallelism must happen at the lemma level (different files), not the attempt level.

## 10. Open Questions and Technical Debt

### Open Questions

- **Model selection.** Currently hardcoded to whatever Claude Code's default model is (Claude Sonnet 4.6 in practice). Should the orchestrator specify `--model` explicitly? Opus would be more capable but 5x more expensive. A per-difficulty model selector could be valuable.

- **Pre-search cost/benefit tradeoff (flagged for future investigation).** Pre-search adds ~$0.002 and ~5K tokens of context. For `fwdDiff_mul` (novel theorem), the result was excellent ($0.35 total, 1 attempt). For `sum_range_id` (Mathlib lookup), cost increased from $0.55 to $0.81 — but this was driven by 2.7x more output tokens (agent verbosity variance), not input token bloat (`cache_creation_input_tokens` was ~25K in both runs). The single before/after comparison does not constitute valid evidence for or against pre-search. **Pre-search is kept as-is.** Re-investigate if any of these conditions arise:
  1. A lemma fails all retry attempts — check whether pre-search results were relevant or misleading (injecting wrong-namespace context could actively hurt).
  2. A pattern emerges where Mathlib-lookup lemmas consistently cost >$0.70 with pre-search — would suggest the extra context is slowing the agent on easy lookups.
  3. Pre-search returns 0 results for a lemma that later succeeds — would indicate the query generation model is producing poor search terms.
  4. Cost tracking across 10+ lemmas shows pre-search runs are systematically more expensive with no accuracy benefit — would justify A/B disabling it.
  Until one of these triggers fires, the current implementation is low-risk ($0.002/call) and not worth optimizing further.

- **Retry strategy.** Currently all retries are uniform — same prompt structure, same budget. A smarter strategy might escalate: simple tactics first, then structured proof, then a different model. This is speculative generality until we hit lemmas that fail multiple attempts.

- **Pocket-level orchestration (Phase 1B).** Running N lemmas in sequence/parallel is the next milestone. The per-lemma pipeline is now validated. The open question is dependency ordering — some lemmas depend on others being proved first.

### Pocket Selection Correctness Note (Discrete Calculus)

The Edge Finder's "Discrete Analogues of Calculus Identities" investigation run (`edge_finder/runs/investigation/run_2026-02-21_151633_discrete_analogues_of_calculus_identities/`) correctly identified a real gap, but the framing was imprecise. Here is the corrected understanding:

**What the Edge Finder got right:**
- `fwdDiff` (Mathlib's forward difference operator) was found and marked `"verified"` (exact name match) in `verification.json`. The tool did not miss it.
- `gap_confidence` was appropriately marked `"low"` with `coverage_ratio` 0.33.
- All three pocket candidates were rated `"moderate"` risk (scores 0.51, 0.44, 0.32). The tool was correctly uncertain.

**What was imprecise:**
- The pocket framing ("Discrete Analogues of Calculus Identities Mini-Library") implied building a new discrete calculus abstraction layer with types like `DiscreteDerivative`, `DiscreteIntegral`, `DiscreteFunction`, and `ShiftOperator`. These are all marked `"absent"` — but they are absent because Mathlib uses `fwdDiff` (a concrete function `(ℕ → G) → (ℕ → G)`) rather than building an abstract type hierarchy. The absence of these names does not mean the functionality is missing; it means the Edge Finder's concept inventory used the wrong names.
- The real pocket is narrower: **theorems about `fwdDiff` that are not yet in `Mathlib.Algebra.Group.ForwardDiff`**. We confirmed one such gap: `fwdDiff_mul` (discrete product rule), which the oracle proved successfully.

**What remains unverified:**
- Other candidate theorems (discrete chain rule, summation by parts, Newton's forward difference formula) need individual LeanExplore verification before assuming they are absent from Mathlib. Do not create lemma specs for these without first searching for them.

**Guidance for future pocket selection:**
- When the Edge Finder reports a pocket with `gap_confidence: "low"`, always verify individual theorem gaps via LeanExplore before committing to a batch of lemma specs.
- Check whether "absent" concepts are truly absent functionality or just absent *names* (Mathlib may implement the same thing under a different name).
- The Edge Finder's `verification.json` entries for `fwdDiff` (showing `fwdDiff_finset_sum`, `fwdDiff_iter_finset_sum`, `shift_eq_sum_fwdDiff_iter`, `fwdDiff_iter_eq_sum_shift`) are the ground truth for what already exists.

### Technical Debt

- **`END_REASON` parsing is fragile.** The agent wraps it in backticks, the regex handles this, but other markdown formatting (bold, code blocks) could break it. A more robust approach: define a structured JSON output schema via `--json-schema`.

- **No timeout tuning per difficulty.** Easy lemmas get the same 15-minute timeout as hard ones. Easy lemmas typically finish in <2 minutes.

- **Verifier timeout is 600s.** First-ever compilation of a file with `import Mathlib` can be slow. Subsequent runs use the cache. The timeout is generous but could be tuned.

- **lean-explore API key in `.mcp.json` args.** This is a workaround for a bug in lean-explore where the `LEANEXPLORE_API_KEY` env var isn't forwarded from the CLI wrapper to the MCP server subprocess. If lean-explore fixes this upstream, we should switch to env-var-only configuration.

- **LeanExplore API ignores `limit` parameter.** The API returns 50 results per query regardless of the `limit` value. We slice client-side to `RESULTS_PER_QUERY` (5) and cap total results at `MAX_TOTAL_RESULTS` (15). If the API fixes this, the client-side cap is still a safety net.

- **No structured output validation.** The agent's proof is whatever it writes to the file. We don't parse or validate the proof structure — we rely entirely on `lake env lean`. This is correct (the compiler is the truth) but means we can't give targeted feedback like "your theorem statement changed."

### Resolved Items (from Phase 1)

- **Pre-search context.** Now implemented via `pre_search.py`. Uses Sonnet 4 for query generation (~$0.002) + LeanExplore API for search. Results are injected into every attempt prompt.

- **No cost tracking in MANIFEST.** Now implemented. `LemmaEntry.cost_usd` accumulates pre-search + session costs. Displayed in MANIFEST.md as `- cost: $X.XXXX`.

### Validated Results (5/5 lemma proofs, 4 unique theorems)

| Lemma | Phase | Pre-search | Difficulty | Attempts | Cost | Duration | Notes |
|-------|-------|-----------|-----------|----------|------|----------|-------|
| `fwdDiff_linear` | 1 | No | easy | 1/10 | $0.09 | 64s | `simp; ring` |
| `div_mod_unique` | 1 | No | medium | 1/10 | $0.56 | 231s | Mathlib lookup (circular) |
| `sum_range_id` | 1 | No | medium | 1/10 | $0.55 | 180s | Mathlib lookup (circular) |
| **`fwdDiff_mul`** | **2** | **Yes** | **medium** | **1/10** | **$0.35** | **92s** | **Novel theorem (not in Mathlib)** |
| `sum_range_id` | 2 | Yes | medium | 1/10 | $0.81 | 241s | Re-run with pre-search |

**Key result:** `fwdDiff_mul` (discrete product rule: Δ(fg)(n) = f(n+1)·Δg(n) + g(n)·Δf(n)) is the first genuinely novel theorem proved by the oracle. It does not exist in Mathlib and required real proof synthesis (`simp [fwdDiff]; ring`). This validates that the pipeline works for actual proof generation, not just Mathlib lookups.
