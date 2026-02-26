# Library Weaver — Walkthrough

## 1. What This Subsystem Does (One Paragraph)

Library Weaver is the orchestration layer that connects Library Architect (which produces a blueprint) to Proof Oracle (which proves individual lemmas). Given a blueprint directory containing `blueprint.json` and `lemma_specs/`, the weaver walks the dependency DAG in topological order, seeds target Lean files with headers and existing definitions, invokes `run_lemma()` for each planned entry, snapshots files before each attempt so failures can be rolled back, propagates failures to skip dependent entries, and produces both JSON and Markdown run reports. It contains zero LLM logic — every decision is deterministic. The output is a set of verified Lean 4 source files forming a complete library.

---

## 2. The Mental Model

Think of Library Weaver as an assembly line manager in a factory:

1. The **blueprint** is the manufacturing order — it specifies which parts to make, in what order, and which parts depend on other parts being finished first.
2. The **DAG walker** is the floor supervisor — it decides which workstation to activate next and shuts down downstream stations when an upstream one breaks.
3. The **file manager** is the stockroom — it prepares blank workpieces (seeded files), takes safety photos before work begins (snapshots), and can restore a workpiece to its pre-work state if the work fails.
4. The **Proof Oracle** is the worker at the station — it receives a spec and a partially-built file, and either produces a verified proof or reports failure.
5. The **report generator** is the quality inspector — it logs what happened at every station and produces a final summary.

The key insight: the weaver is **dumb on purpose**. It does not reason about mathematics. It does not decide what tactics to use. It does not retry proofs. It simply walks a plan and records what happens. All intelligence is pushed to the Oracle (proof search) or the Architect (plan creation).

Data flows in one direction:

```
blueprint.json ──▶ WeavePlan ──▶ DAGWalker ──▶ proof loop ──▶ WeaveResult
                                                   │
                                            FileManager (snapshot/restore)
                                                   │
                                            Proof Oracle (run_lemma)
```

---

## 3. Directory Structure Explained

```
library_weaver/
├── __init__.py          # Package docstring (1 line)
├── __main__.py          # Enables `python -m library_weaver` (5 lines)
├── cli.py               # Argument parsing, thin wrapper around weave() (95 lines)
├── models.py            # Data models: PlannedEntry, ExistingEntry, WeavePlan, etc. (239 lines)
├── loader.py            # Parses blueprint.json → WeavePlan (221 lines)
├── dag.py               # DAGWalker: topological traversal + failure propagation (117 lines)
├── file_manager.py      # File seeding, snapshotting, restoring (143 lines)
├── weaver.py            # Main orchestration loop (354 lines)
├── report.py            # JSON + Markdown report generation (110 lines)
├── docs/
│   └── library_weaver_design.md    # Phase 1 design document (1118 lines)
└── runs/
    └── <run_id>/
        ├── weave_report.json       # Machine-readable results (updated per-entry)
        ├── WEAVE_REPORT.md         # Human-readable summary
        └── file_snapshots/         # Pre-attempt file copies
```

**Total implementation**: 7 modules, ~1,284 lines of Python.

The `runs/` directory grows over time. Each invocation creates a new `<run_id>/` subdirectory with a timestamp-based name (e.g. `graded_order_combinatorics_20260226T164808Z`).

---

## 4. Call Graph Explanation

```
cli.main()
  └── weaver.weave(blueprint_dir, project_root, ...)
        ├── loader.load_blueprint(blueprint_dir)
        │     ├── _parse_planned_entry(raw)          # for each planned entry
        │     ├── _resolve_existing_entries(raw, planned)
        │     │     └── _find_first_dependent(name, planned)
        │     └── _validate(entries, names, spec_dir)
        │
        ├── DAGWalker.__init__(plan, pre_done)       # build status dict + reverse DAG
        ├── FileManager.__init__(project_root, run_dir)
        │
        ├── FileManager.seed_file(target, ns, theme, layer)    # for each target file
        ├── FileManager.write_definition(existing)              # for each existing entry
        │
        └── [proof loop]
              ├── walker.next_entry()                 # get next pending entry
              ├── FileManager.snapshot(target_file)    # save pre-attempt state
              ├── proof_oracle.run_lemma(spec_path)    # THE CALL — blocks until done
              │
              ├── [on success]
              │     └── walker.mark_done(name)
              ├── [on failure]
              │     ├── FileManager.restore(target_file, snapshot_id)
              │     ├── walker.mark_failed(name)
              │     └── walker._propagate_skip(name)   # BFS over reverse DAG
              │
              ├── report.write_json_report(result, run_dir)   # after each entry
              └── walker.advance()
        │
        ├── report.write_json_report(result, run_dir)  # final
        └── report.write_markdown_report(result, run_dir)
```

The critical path is: `load_blueprint` → `seed_file` (per file) → `next_entry` → `snapshot` → `run_lemma` → `mark_done/mark_failed` → `write_json_report` → repeat.

---

## 5. Execution Lifecycle Walkthrough

### Phase A: Setup

1. **CLI parsing** (`cli.py:22-62`): `argparse` parses `blueprint_dir`, `--project-root`, `--run-dir`, `--dry-run`, and `--done`. The `--done` flag is a comma-separated list of entry names for resume support.

2. **Blueprint loading** (`loader.py:26-117`): Reads `blueprint.json`, separates entries by status (`planned` vs `exists_in_mathlib`), extracts `target_file`/`target_namespace` from the nested `lemma_spec` object, builds the internal dependency graph (planned-to-planned edges only), and validates that all spec files exist.

3. **Run directory creation** (`weaver.py:58-63`): Creates `library_weaver/runs/<theme>_<timestamp>/` with `file_snapshots/` subdirectory.

4. **Component initialization** (`weaver.py:68-69`): Creates `FileManager` and `DAGWalker`. If `--done` was provided, the walker pre-marks those entries as `done`.

### Phase B: File Seeding

5. **Seed target files** (`weaver.py:97-122`): For each unique `target_file` in the plan, creates a Lean file with:
   - A header comment (theme, layer)
   - `import Mathlib`
   - `namespace <ns>` / `end <ns>` block
   - A placeholder comment

   If the file already exists (from a previous run or manual work), seeding is skipped.

6. **Write existing definitions** (`weaver.py:127-132`): For `exists_in_mathlib` entries, inserts their `suggested_signature` into the appropriate file before the closing `end` line. This ensures downstream planned entries can reference them.

### Phase C: Proof Loop

7. **Get next entry** (`dag.py:54-65`): The walker returns the next `pending` entry by cursor position (entries are in topological order). Entries already resolved as `done`, `failed`, or `skipped` are skipped over.

8. **Snapshot** (`file_manager.py:109-124`): The target file is copied to `file_snapshots/` with a sequential ID. This is the rollback point.

9. **Invoke Oracle** (`weaver.py:195-196`): Calls `proof_oracle.runner.orchestrator.run_lemma(spec_path, project_root=project_root)`. This is a blocking call that spawns a Claude Code session, which writes the proof and verifies it with `lake env lean`. Returns `True` or `False`.

10. **Handle result** (`weaver.py:240-266`):
    - **Success**: Mark `done` in the walker. The proven code is already in the target file (the Oracle wrote it). The next entry will see it.
    - **Failure**: Restore the file from snapshot (undo any partial/corrupt writes). Mark `failed` in the walker. The walker's `_propagate_skip()` BFS marks all transitive dependents as `skipped`.
    - **Exception (crash)**: Same as failure, plus logs the error message.
    - **CreditExhaustedError**: Restore file, log the entry as failed, halt the run (do not propagate skips — the problem is infrastructure, not proof).
    - **SIGINT**: Restore current file, save JSON report, print resume command.

11. **Write checkpoint** (`weaver.py:266`): After every entry (success or failure), the JSON report is overwritten. This provides crash safety — if the process dies, the JSON report reflects all completed entries.

### Phase D: Finalization

12. **Write reports** (`weaver.py:283-297`): Compute total duration, write final JSON report and Markdown report. Print summary to stdout.

### Resume Flow

To resume an interrupted run:
```
python -m library_weaver <blueprint_dir> \
  --done entry1,entry2,entry3
```

The `--done` entries are pre-marked in the walker. The proof loop skips them and processes only remaining pending entries. File seeding is also idempotent (skips existing files).

---

## 6. Annotated Excerpts of Key Functions

### Blueprint Loading: Separating Planned from Existing

```python
# loader.py:61-72
for raw in raw_entries:
    status = raw.get("status", "planned")
    if status == "planned":
        entry = _parse_planned_entry(raw)   # Extract from nested lemma_spec
        planned_entries.append(entry)
        planned_names.add(entry.name)
    elif status == "exists_in_mathlib":
        existing_entries_raw.append(raw)
```

The blueprint contains two kinds of entries. `planned` entries need proofs; `exists_in_mathlib` entries are Mathlib definitions that must be seeded into files so planned entries can reference them. The loader separates them here.

### DAG Failure Propagation

```python
# dag.py:95-116
def _propagate_skip(self, failed_name: str) -> None:
    queue = list(self._dependents.get(failed_name, set()))
    visited: set[str] = set()
    while queue:
        name = queue.pop(0)
        if name in visited:
            continue
        visited.add(name)
        if self._status[name] == "pending":
            self._status[name] = "skipped"
            self._skip_reasons[name] = f"dependency failed: {failed_name}"
        for dep in self._dependents.get(name, set()):
            if dep not in visited:
                queue.append(dep)
```

BFS over the **reverse** DAG (dependents, not dependencies). When `rankGenPoly` fails, everything that transitively depends on it (`rankGenPoly_eval_one`, `rankGenPoly_coeff`, etc.) is immediately marked `skipped`. This prevents wasting Oracle invocations on entries that cannot succeed.

### Snapshot and Restore

```python
# file_manager.py:109-135
def snapshot(self, target_file: str) -> str:
    full_path = self._project_root / target_file
    self._snapshot_counter += 1
    snapshot_id = f"snap_{self._snapshot_counter:04d}"
    safe_name = target_file.replace("/", "_")
    snapshot_path = self._snapshot_dir / f"{safe_name}_{snapshot_id}.lean"
    shutil.copy2(str(full_path), str(snapshot_path))
    return snapshot_id

def restore(self, target_file: str, snapshot_id: str) -> None:
    full_path = self._project_root / target_file
    safe_name = target_file.replace("/", "_")
    snapshot_path = self._snapshot_dir / f"{safe_name}_{snapshot_id}.lean"
    shutil.copy2(str(snapshot_path), str(full_path))
```

Simple file copies. Each Lean file is ~50-120 lines, so copies are trivial. The snapshot ID is a sequential counter, not a hash — we only need the most recent snapshot per attempt, and the sequential ordering provides a natural audit trail.

### SIGINT Graceful Shutdown

```python
# weaver.py:87-92, 268-276
def _sigint_handler(signum, frame):
    raise GracefulExit()

signal.signal(signal.SIGINT, _sigint_handler)

# ...in the proof loop:
except GracefulExit:
    print("\n\nInterrupted by user. Saving progress...")
    if current_snapshot_id and current_target_file:
        file_mgr.restore(current_target_file, current_snapshot_id)
    write_json_report(result, run_dir)
```

Ctrl+C raises `GracefulExit` (a custom exception), which is caught by the outer try/except. The current file is restored to its pre-attempt state, the JSON report is saved with all completed entries, and a resume command is printed.

---

## 7. Critical Invariants

1. **Topological order is maintained.** Entries are sorted by `order_index` (from the Library Architect's assembler). The DAG walker processes them in this order. An entry is never attempted before all its dependencies have been resolved (as `done`, `failed`, or `skipped`).

2. **Files grow monotonically on success.** When an entry is proved, its code is appended to the target file by the Oracle. The weaver never removes proven code. This means each subsequent Oracle invocation sees all previously proven results.

3. **Files are restored on failure.** If the Oracle fails or crashes, the file is restored to its pre-attempt snapshot. The file never contains partial or corrupt proof attempts after a failure.

4. **The JSON report reflects all completed work.** After every entry (success or failure), the JSON report is overwritten. If the process crashes between entries, no work is lost — all prior results are persisted.

5. **Failure propagation is transitive.** When entry X fails, all entries reachable from X in the reverse DAG are marked `skipped`. This is complete (BFS) and immediate (happens before the next entry is considered).

6. **The weaver never modifies specs.** It reads `LemmaSpec` files and passes their paths to the Oracle. It does not adjust signatures, hints, budgets, or any other spec fields.

7. **Seeding and definition writing are idempotent.** Running the weaver twice with the same blueprint does not duplicate headers, definitions, or namespace blocks.

---

## 8. Things That Must Not Be Broken

1. **The snapshot-restore cycle.** If `snapshot()` is called before `run_lemma()` and `restore()` is called on failure, the file returns to its exact pre-attempt state. Breaking this invariant means a failed proof attempt can corrupt the file for all subsequent entries.

2. **The dependency between `loader.py` and `blueprint.json` structure.** The loader assumes `target_file` and `target_namespace` are nested inside `lemma_spec`, not at the top level. If the Library Architect changes its output format, the loader will silently produce wrong `PlannedEntry` objects.

3. **The `order_index` sort in `loader.py:76`.** This ensures topological order even if `blueprint.json` entries are reordered. Removing this sort could cause the weaver to attempt entries before their dependencies.

4. **The `planned_names` filter in the DAG (`loader.py:90-91`).** Dependencies that reference `exists_in_mathlib` entries are filtered out of the internal DAG. This is correct because existing entries don't need proving. If this filter is removed, the walker will look for entries that don't exist in its status dict and crash.

5. **The SIGINT handler restoration (`weaver.py:278`).** The `finally` block restores the original signal handler. If this is removed, the custom handler persists after `weave()` returns, which would break any calling code that expects normal SIGINT behavior.

6. **The `end <namespace>` marker in `file_manager.py:100-105`.** Definition writing inserts code before this marker. If the marker is missing (e.g., the file was manually edited), the definition is silently not written, and downstream entries that depend on it will fail with mysterious Lean errors.

---

## 9. Most Dangerous Refactor Mistakes

1. **Moving `run_lemma()` import to module level.** Currently imported inside the proof loop (`weaver.py:195`) to avoid import errors when the Oracle is not installed. Moving it to the top of the file would break `--dry-run` and any use of the weaver without a working Oracle installation.

2. **Making file operations async without locking.** If parallelism is added, multiple Oracle invocations could write to the same target file concurrently. The snapshot-restore cycle assumes exclusive access to each file. Adding async without file-level locks will cause data races.

3. **Changing `PlannedEntry` from frozen to mutable.** The weaver passes `PlannedEntry` objects to multiple components. If they become mutable, one component modifying an entry could corrupt another component's state.

4. **Removing the `write_json_report()` call inside the proof loop.** This per-entry checkpoint is crash safety. Without it, a crash after 10 successful entries would lose all 10 results.

5. **Adding retry logic to the weaver.** The Oracle manages its own retry budget internally. If the weaver also retries (calling `run_lemma()` multiple times for the same entry), the snapshot-restore cycle would need to be restructured, and the report would need to track multiple attempts per entry. The current architecture assumes `run_lemma()` is called exactly once per entry per run.

6. **Reordering the `mark_failed` → `_propagate_skip` → `advance` sequence.** These three operations must happen in this exact order. If `advance()` happens before `_propagate_skip()`, the walker might serve a skipped entry as the next entry. If `_propagate_skip()` happens before `mark_failed()`, the BFS starting node won't have the right status.

---

## 10. Open Questions and Technical Debt

### Open Questions

1. **Should the weaver support partial file targets?** Currently, all entries in a file are processed sequentially. If a file has 6 entries and entry 3 fails, entries 4-6 are skipped (if dependent). Should the weaver try entries 4-6 if they are independent of entry 3? Currently it does — the DAG is entry-level, not file-level. But this means an independent entry 5 might be attempted against a file that is "missing" entry 3's proof. This works only because the spec is self-contained and the Oracle writes the proof at a specific location.

2. **Should snapshots be retained or cleaned up?** Currently all snapshots are kept in `file_snapshots/`. For a large run, this could produce many small files. A cleanup step (delete snapshots for successfully proven entries) would reduce clutter but lose the audit trail.

3. **What happens if `blueprint.json` changes between runs?** The resume mechanism (`--done`) pre-marks entries by name. If entry names change, the pre-marking silently does nothing. There is no checksum or version check on the blueprint.

### Technical Debt

1. **Line 284 of `weaver.py`** contains `total_time = time.time() - time.time()` — a no-op that always produces 0. The actual duration is correctly computed from ISO timestamps on lines 287-289, so this line is dead code but should be removed.

2. **No unit tests.** The weaver was validated by running it against the Graded Order Combinatorics blueprint (the real end-to-end test). Unit tests for `DAGWalker`, `FileManager`, and `loader` would catch regressions. The `DAGWalker` in particular has non-trivial BFS logic that should be tested with crafted dependency graphs.

3. **No logging framework.** All output goes through `print()`. For production use, a proper logger (with configurable levels and file output) would be more appropriate.

4. **`_find_first_dependent` is O(n).** For each `exists_in_mathlib` entry, it scans all planned entries. For the current blueprint (18 entries) this is trivial. For a 500-entry blueprint it would still be fast, but the nested loop pattern is inelegant.

5. **`CreditExhaustedError` is imported from `proof_oracle`** at module level (`weaver.py:25`). This creates a hard dependency on the Oracle's internal exception hierarchy. If the Oracle refactors its exceptions, the weaver breaks at import time.

6. **The markdown report formatting** (`report.py:60-65`) has hardcoded column widths that don't adapt to large numbers. A count of 100+ would misalign the table.
