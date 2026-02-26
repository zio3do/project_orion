"""
Weaver Core — the main orchestration loop for Library Weaver.

Reads a blueprint, walks the dependency DAG in topological order,
manages Lean file accumulation, invokes the Proof Oracle for each
entry, and produces a complete verified Lean 4 library (or a partial
library with clear failure reporting).

This module contains no LLM logic — every decision is deterministic.
The Oracle handles proof search; the weaver handles coordination.
"""

from __future__ import annotations

import signal
import time
from datetime import datetime, timezone
from pathlib import Path

from library_weaver.dag import DAGWalker
from library_weaver.file_manager import FileManager
from library_weaver.loader import load_blueprint
from library_weaver.models import EntryResult, WeaveResult
from library_weaver.report import write_json_report, write_markdown_report
from proof_oracle.runner.orchestrator import CreditExhaustedError  # type: ignore


class GracefulExit(Exception):
    """Raised by the SIGINT handler to allow clean shutdown."""


def weave(
    blueprint_dir: Path,
    project_root: Path | None = None,
    run_dir: Path | None = None,
    dry_run: bool = False,
    done_entries: frozenset[str] | None = None,
) -> WeaveResult:
    """Execute a blueprint end-to-end.

    Args:
        blueprint_dir: Path to Library Architect output (contains blueprint.json).
        project_root: Lean project root. Defaults to cwd.
        run_dir: Where to store run artifacts. Auto-generated if None.
        dry_run: If True, print the execution plan without invoking the Oracle.
        done_entries: Entry names to pre-mark as done (for resuming a previous run).

    Returns:
        WeaveResult with per-entry outcomes and aggregate statistics.
    """
    if project_root is None:
        project_root = Path.cwd()

    # ------------------------------------------------------------------
    # 1. Load blueprint
    # ------------------------------------------------------------------
    plan = load_blueprint(blueprint_dir)
    now_str = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_id = f"{plan.theme.lower().replace(' ', '_')}_{now_str}"

    if run_dir is None:
        run_dir = Path(__file__).resolve().parent / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    # ------------------------------------------------------------------
    # 2. Initialize components
    # ------------------------------------------------------------------
    file_mgr = FileManager(project_root, run_dir)
    walker = DAGWalker(plan, pre_done=done_entries)

    result = WeaveResult(
        run_id=run_id,
        theme=plan.theme,
        blueprint_path=str(plan.blueprint_path),
    )

    # ------------------------------------------------------------------
    # Dry-run: print plan and exit
    # ------------------------------------------------------------------
    if dry_run:
        _print_dry_run(plan, walker)
        return result

    # ------------------------------------------------------------------
    # 3. Install SIGINT handler
    # ------------------------------------------------------------------
    original_handler = signal.getsignal(signal.SIGINT)

    def _sigint_handler(signum, frame):  # noqa: ARG001
        raise GracefulExit()

    signal.signal(signal.SIGINT, _sigint_handler)

    # ------------------------------------------------------------------
    # 4. Seed target files
    # ------------------------------------------------------------------
    print(f"\nSeeding target files...")
    for target_file, entry_names in plan.target_files.items():
        # Use the namespace and layer from the first entry in this file
        first_entry = next(
            (e for e in plan.entries if e.target_file == target_file), None
        )
        if first_entry is None:
            # File only has existing entries — use existing entry info
            existing = next(
                (e for e in plan.existing_entries if e.target_file == target_file),
                None,
            )
            if existing:
                ns = existing.target_namespace
                layer = existing.layer
            else:
                continue
        else:
            ns = first_entry.target_namespace
            layer = first_entry.layer

        created = file_mgr.seed_file(target_file, ns, plan.theme, layer)
        if created:
            print(f"  Created: {target_file}")
        else:
            print(f"  Exists:  {target_file}")

    # ------------------------------------------------------------------
    # 5. Write exists_in_mathlib definitions
    # ------------------------------------------------------------------
    for existing in plan.existing_entries:
        written = file_mgr.write_definition(existing)
        if written:
            print(f"  Wrote definition: {existing.name} (exists_in_mathlib)")
        else:
            print(f"  Definition present: {existing.name} (exists_in_mathlib)")

    # ------------------------------------------------------------------
    # 6. Proof loop
    # ------------------------------------------------------------------
    result.started = datetime.now(timezone.utc).isoformat()
    total = len(plan.entries)
    entry_index = 0
    current_snapshot_id: str | None = None
    current_target_file: str | None = None

    print(f"\nStarting proof loop ({total} entries)...\n")

    # Log pre-done entries from resume
    if done_entries:
        pre_done_in_plan = [e.name for e in plan.entries if e.name in done_entries]
        if pre_done_in_plan:
            print(f"  Resuming: {len(pre_done_in_plan)} entries pre-marked as done:")
            for name in pre_done_in_plan:
                print(f"    ✓ {name}")
            print()

    try:
        while True:
            entry = walker.next_entry()
            if entry is None:
                break

            entry_index += 1
            status = walker.status(entry.name)

            # --- Skipped entries ---
            if status == "skipped":
                reason = walker.skip_reason(entry.name)
                print(f"[{entry_index:2d}/{total}] {entry.name} — SKIPPED ({reason})")
                result.entry_results.append(EntryResult(
                    name=entry.name,
                    status="skipped",
                    target_file=entry.target_file,
                    difficulty=entry.difficulty,
                    skip_reason=reason,
                ))
                walker.advance()
                write_json_report(result, run_dir)
                continue

            # --- Attempt proof ---
            print(f"[{entry_index:2d}/{total}] {entry.name} ({entry.difficulty}) → "
                  f"{Path(entry.target_file).name}")

            # Snapshot before Oracle invocation
            current_target_file = entry.target_file
            current_snapshot_id = file_mgr.snapshot(entry.target_file)

            spec_path = plan.spec_dir / entry.spec_file
            print(f"  Invoking Proof Oracle...")

            start_time = time.time()
            success = False

            try:
                # Import here to avoid import errors when Oracle is not installed.
                # CreditExhaustedError is imported at module level above.
                from proof_oracle.runner.orchestrator import run_lemma  # type: ignore
                success = run_lemma(spec_path, project_root=project_root)
            except GracefulExit:
                raise  # Re-raise to the outer handler
            except CreditExhaustedError as exc:
                # Credit exhaustion is an infrastructure error — halt the run.
                # Restoring the file and saving progress is handled by the
                # outer GracefulExit-style cleanup below.
                elapsed = time.time() - start_time
                print(f"  CREDIT EXHAUSTION: {exc}")
                file_mgr.restore(entry.target_file, current_snapshot_id)
                result.entry_results.append(EntryResult(
                    name=entry.name,
                    status="failed",
                    target_file=entry.target_file,
                    difficulty=entry.difficulty,
                    duration_seconds=elapsed,
                    error_message=str(exc),
                ))
                write_json_report(result, run_dir)
                print("\n  Halting run — Claude API credits exhausted. "
                      "Replenish credits and resume.")
                break
            except Exception as exc:
                elapsed = time.time() - start_time
                print(f"  CRASH: {entry.name}: {exc}")
                file_mgr.restore(entry.target_file, current_snapshot_id)
                walker.mark_failed(entry.name)
                result.entry_results.append(EntryResult(
                    name=entry.name,
                    status="failed",
                    target_file=entry.target_file,
                    difficulty=entry.difficulty,
                    duration_seconds=elapsed,
                    error_message=str(exc),
                ))
                _log_skipped_dependents(walker, plan, entry.name)
                walker.advance()
                current_snapshot_id = None
                current_target_file = None
                write_json_report(result, run_dir)
                continue

            elapsed = time.time() - start_time

            if success:
                print(f"  DONE ({_format_short(elapsed)})")
                walker.mark_done(entry.name)
                result.entry_results.append(EntryResult(
                    name=entry.name,
                    status="done",
                    target_file=entry.target_file,
                    difficulty=entry.difficulty,
                    duration_seconds=elapsed,
                ))
            else:
                print(f"  FAILED ({_format_short(elapsed)})")
                file_mgr.restore(entry.target_file, current_snapshot_id)
                walker.mark_failed(entry.name)
                result.entry_results.append(EntryResult(
                    name=entry.name,
                    status="failed",
                    target_file=entry.target_file,
                    difficulty=entry.difficulty,
                    duration_seconds=elapsed,
                ))
                _log_skipped_dependents(walker, plan, entry.name)

            walker.advance()
            current_snapshot_id = None
            current_target_file = None
            write_json_report(result, run_dir)

    except GracefulExit:
        print("\n\nInterrupted by user. Saving progress...")
        if current_snapshot_id and current_target_file:
            file_mgr.restore(current_target_file, current_snapshot_id)
            print(f"  Restored {current_target_file} to pre-attempt state.")
        write_json_report(result, run_dir)
        print(f"  Progress saved to {run_dir / 'weave_report.json'}")
        print(f"  Resume with: python -m library_weaver {blueprint_dir} --resume {run_id}")

    finally:
        signal.signal(signal.SIGINT, original_handler)

    # ------------------------------------------------------------------
    # 7. Finalize
    # ------------------------------------------------------------------
    result.finished = datetime.now(timezone.utc).isoformat()
    total_time = time.time() - time.time()  # will be set properly below

    if result.started:
        start_dt = datetime.fromisoformat(result.started)
        end_dt = datetime.fromisoformat(result.finished)
        result.duration_seconds = (end_dt - start_dt).total_seconds()

    write_json_report(result, run_dir)
    md_path = write_markdown_report(result, run_dir)

    summary = walker.summary()
    print(f"\nWeave complete: {summary['done']}/{total} proved, "
          f"{summary['failed']} failed, {summary['skipped']} skipped")
    print(f"Report: {md_path}")

    return result


def _print_dry_run(plan, walker) -> None:
    """Print the execution plan without invoking the Oracle."""
    print(f"\nLibrary Weaver (dry run)")
    print(f"Blueprint: {plan.blueprint_path}")
    print(f"Theme: {plan.theme}")
    print(f"Planned entries: {len(plan.entries)}"
          f" ({len(plan.existing_entries)} exists_in_mathlib)")
    print()

    print("Target files to create:")
    for tf, names in plan.target_files.items():
        print(f"  {tf} ({len(names)} entries)")
    print()

    if plan.existing_entries:
        print("Definitions to seed (exists_in_mathlib):")
        for e in plan.existing_entries:
            print(f"  - {e.name} → {Path(e.target_file).name} "
                  f"(ref: {e.mathlib_reference})")
        print()

    print("Entries in execution order:")
    for i, entry in enumerate(plan.entries, 1):
        internal_deps = plan.dag[entry.name]
        if internal_deps:
            dep_str = ", ".join(internal_deps)
        else:
            dep_str = "(external only)"
        print(f"  [{i:2d}/{len(plan.entries)}] {entry.name:35s} "
              f"{entry.difficulty:6s} {Path(entry.target_file).name:25s} "
              f"deps: {dep_str}")

    print(f"\nDry run complete. No proofs attempted.")


def _log_skipped_dependents(walker, plan, failed_name: str) -> None:
    """Log which entries were skipped due to a failure."""
    skipped = [
        e.name for e in plan.entries
        if walker.status(e.name) == "skipped"
        and walker.skip_reason(e.name) == f"dependency failed: {failed_name}"
    ]
    if skipped:
        print(f"  Skipping dependents: {', '.join(skipped)}")


def _format_short(seconds: float) -> str:
    """Short duration format for inline logging."""
    if seconds < 60:
        return f"{seconds:.0f}s"
    minutes = int(seconds // 60)
    remaining = int(seconds % 60)
    return f"{minutes}m {remaining:02d}s"
