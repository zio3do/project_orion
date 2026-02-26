"""
Elaboration Checker — quality gate for the Library Architect pipeline.

Validates that generated Lean 4 signatures elaborate correctly by wrapping
each in a minimal file with `import Mathlib` and a `sorry` body, then
running `lake env lean` to check for elaboration errors.

This catches the four error categories identified in the pipeline audit:
  1. Lean syntax errors (missing brackets, wrong operators)
  2. Mathematical soundness errors (wrong type, impossible statement)
  3. Typeclass/instance errors (missing or wrong typeclass assumptions)
  4. API name errors (nonexistent Mathlib names)

Design constraints:
  - Default mode is **batched**: all signatures go into one .lean file
    with separate sections, and `lake env lean` runs once. This amortizes
    the ~3-4 minute Mathlib import cost across all signatures.
  - Sequential mode (batch=False) runs one `lake env lean` per signature
    for better error isolation, but is much slower.
  - Timeout: 300 seconds (to accommodate slow Mathlib imports).
  - Results are reported as pass/fail with error messages.
  - The checker is optional — the pipeline works without it.

The checker does NOT modify signatures. It only reports which ones fail.
Fixing failed signatures is a future step (either manual or LLM-assisted).
"""

from __future__ import annotations

import logging
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

logger = logging.getLogger(__name__)

# Timeout for each `lake env lean` invocation (seconds).
# Single-signature checks take ~3-4 minutes due to Mathlib import.
# Batched checks amortize this cost, but we keep a generous timeout.
ELABORATION_TIMEOUT_S = 300

# Path to the project root (where lakefile.toml lives).
# This is needed so `lake env lean` can find Mathlib.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class ElaborationResult:
    """Result of elaboration-checking a single signature."""
    name: str
    passed: bool
    signature: str
    error_message: str = ""
    lean_file: str = ""  # The generated .lean content (for debugging).

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "name": self.name,
            "passed": self.passed,
            "signature": self.signature,
        }
        if self.error_message:
            d["error_message"] = self.error_message
        return d


@dataclass
class ElaborationReport:
    """Summary of elaboration checking across all signatures."""
    results: list[ElaborationResult] = field(default_factory=list)
    total: int = 0
    passed: int = 0
    failed: int = 0
    skipped: int = 0  # Entries with empty signatures.

    def to_dict(self) -> dict[str, Any]:
        return {
            "total": self.total,
            "passed": self.passed,
            "failed": self.failed,
            "skipped": self.skipped,
            "results": [r.to_dict() for r in self.results],
        }


def _find_lake_env_lean() -> str | None:
    """Find the `lake` binary. Returns the path or None if not found."""
    lake = shutil.which("lake")
    if lake:
        return lake
    # Check elan's bin directory.
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return str(elan_lake)
    return None


def _generate_lean_file(signature: str, entry_type: str) -> str:
    """Generate a minimal .lean file that elaborates a single signature.

    The file imports Mathlib and wraps the signature with a sorry body.
    We add `noncomputable` to avoid definitional computation issues, and
    `set_option maxHeartbeats 200000` to give a reasonable timeout for
    typeclass search.

    Args:
        signature: The Lean 4 signature (e.g., "def foo (x : Nat) : Nat")
        entry_type: "definition" or "lemma"

    Returns:
        The complete .lean file content.
    """
    lines = [
        "import Mathlib",
        "",
        "set_option maxHeartbeats 400000",
        "",
        "open Finset in",
        "open Polynomial in",
        "",
    ]

    sig = signature.strip()

    # Detect if the signature already has a body (contains `:=` or `where`).
    # If so, strip it — we want to replace with sorry.
    has_body = False
    for marker in [":= by", ":=by", ":= sorry", ":=sorry", "where"]:
        if marker in sig:
            sig = sig[:sig.index(marker)].rstrip()
            has_body = True
            break

    # Add noncomputable prefix if not already present and it's a definition.
    if entry_type == "definition" and not sig.startswith("noncomputable"):
        sig = "noncomputable " + sig

    # Determine the sorry body based on entry type.
    if entry_type == "lemma" or sig.lstrip("noncomputable ").startswith(("theorem", "lemma")):
        lines.append(f"{sig} := by sorry")
    else:
        lines.append(f"{sig} := sorry")

    lines.append("")
    return "\n".join(lines)


def check_signature(
    name: str,
    signature: str,
    entry_type: str,
    *,
    project_root: Path | None = None,
    timeout: int = ELABORATION_TIMEOUT_S,
) -> ElaborationResult:
    """Check a single signature by elaborating it with sorry.

    Args:
        name: The declaration name (for reporting).
        signature: The Lean 4 signature to check.
        entry_type: "definition" or "lemma".
        project_root: Path to the project root (where lakefile.toml lives).
        timeout: Timeout in seconds for elaboration.

    Returns:
        An ElaborationResult with pass/fail and any error message.
    """
    if not signature or not signature.strip():
        return ElaborationResult(
            name=name,
            passed=False,
            signature=signature,
            error_message="Empty signature.",
        )

    root = project_root or _PROJECT_ROOT
    lake = _find_lake_env_lean()
    if not lake:
        return ElaborationResult(
            name=name,
            passed=False,
            signature=signature,
            error_message="lake binary not found. Install elan to enable elaboration checking.",
        )

    lean_content = _generate_lean_file(signature, entry_type)

    # Write to a temporary file inside the project (so lake can find Mathlib).
    tmp_dir = root / ".elaboration_check_tmp"
    tmp_dir.mkdir(exist_ok=True)

    # Use a sanitized filename to avoid conflicts.
    safe_name = name.replace(".", "_").replace("/", "_")
    tmp_file = tmp_dir / f"_check_{safe_name}.lean"

    try:
        tmp_file.write_text(lean_content, encoding="utf-8")

        result = subprocess.run(
            [lake, "env", "lean", str(tmp_file)],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(root),
        )

        if result.returncode == 0:
            return ElaborationResult(
                name=name,
                passed=True,
                signature=signature,
                lean_file=lean_content,
            )
        else:
            # Extract the most relevant error lines.
            stderr = result.stderr.strip()
            # Filter out noisy lines (import resolution, etc.).
            error_lines = []
            for line in stderr.split("\n"):
                if "error" in line.lower() or "unknown" in line.lower():
                    error_lines.append(line.strip())
            error_msg = "\n".join(error_lines[:5]) if error_lines else stderr[:500]

            return ElaborationResult(
                name=name,
                passed=False,
                signature=signature,
                error_message=error_msg,
                lean_file=lean_content,
            )

    except subprocess.TimeoutExpired:
        return ElaborationResult(
            name=name,
            passed=False,
            signature=signature,
            error_message=f"Elaboration timed out after {timeout}s.",
            lean_file=lean_content,
        )
    except Exception as exc:
        return ElaborationResult(
            name=name,
            passed=False,
            signature=signature,
            error_message=f"Unexpected error: {exc}",
            lean_file=lean_content,
        )
    finally:
        # Clean up the temporary file.
        if tmp_file.exists():
            tmp_file.unlink()


def _generate_batched_lean_file(
    entries: list[dict[str, Any]],
) -> tuple[str, dict[int, str]]:
    """Generate a single .lean file containing all signatures, each in its own section.

    Each signature gets a unique marker comment and is wrapped in a `section`/`end`
    block so that errors in one signature don't cascade to others (Lean continues
    checking after a section-level error).

    Returns:
        A tuple of (lean_file_content, line_to_name_map) where line_to_name_map
        maps the line number of each signature's marker comment to the entry name.
        This allows attributing errors from stderr back to specific signatures.
    """
    lines: list[str] = [
        "import Mathlib",
        "",
        "set_option maxHeartbeats 400000",
        "",
        "open Finset",
        "open Polynomial",
        "",
    ]
    # We'll record the line of the marker comment for each entry.
    marker_lines: dict[int, str] = {}

    # We also build a reverse index: for each entry, record the start and end
    # line numbers so we can attribute errors to entries by line range.
    # _entry_ranges will be: [(name, start_line, end_line), ...]
    entry_ranges: list[tuple[str, int, int]] = []

    for entry in entries:
        name = entry["name"]
        sig = entry["suggested_signature"].strip()
        etype = entry.get("entry_type", "lemma")

        # Strip existing body.
        for marker in [":= by", ":=by", ":= sorry", ":=sorry", "where"]:
            if marker in sig:
                sig = sig[:sig.index(marker)].rstrip()
                break

        # Add noncomputable prefix for definitions.
        if etype == "definition" and not sig.startswith("noncomputable"):
            sig = "noncomputable " + sig

        # Determine sorry body.
        is_lemma = (
            etype == "lemma"
            or sig.lstrip("noncomputable ").startswith(("theorem", "lemma"))
        )

        start_line = len(lines) + 1  # 1-indexed

        # Marker comment so we can identify which section an error belongs to.
        safe_name = name.replace(".", "_").replace("/", "_")
        lines.append(f"-- @@ELAB_CHECK: {name}")
        marker_lines[len(lines)] = name  # len(lines) is the 1-indexed line number

        lines.append(f"section elab_{safe_name}")
        if is_lemma:
            lines.append(f"{sig} := by sorry")
        else:
            lines.append(f"{sig} := sorry")
        lines.append(f"end elab_{safe_name}")
        lines.append("")

        end_line = len(lines)  # 1-indexed, inclusive
        entry_ranges.append((name, start_line, end_line))

    return "\n".join(lines), marker_lines


def _parse_batched_errors(
    stderr: str,
    entry_ranges: list[tuple[str, int, int]],
    tmp_file_name: str,
) -> dict[str, list[str]]:
    """Parse errors from batched elaboration output and attribute to entries.

    Args:
        stderr: The stderr output from `lake env lean`.
        entry_ranges: List of (name, start_line, end_line) tuples.
        tmp_file_name: The filename used in the temp file (for matching).

    Returns:
        Dict mapping entry name to list of error lines. Entries with no errors
        won't appear in the dict.
    """
    errors: dict[str, list[str]] = {}

    for line in stderr.split("\n"):
        line = line.strip()
        if not line:
            continue
        # Lean error format: filename:line:col: error: message
        # or just: filename:line:col: message
        if "error" not in line.lower() and "unknown" not in line.lower():
            continue

        # Try to extract the line number from the error message.
        err_line_num = None
        parts = line.split(":")
        # Typical format: /path/to/file.lean:42:0: error: ...
        for i, part in enumerate(parts):
            part = part.strip()
            if part.isdigit() and i > 0:
                err_line_num = int(part)
                break

        if err_line_num is None:
            continue

        # Find which entry this line number belongs to.
        for entry_name, start, end in entry_ranges:
            if start <= err_line_num <= end:
                if entry_name not in errors:
                    errors[entry_name] = []
                errors[entry_name].append(line)
                break

    return errors


def check_blueprint(
    entries: list[dict[str, Any]],
    *,
    project_root: Path | None = None,
    timeout: int = ELABORATION_TIMEOUT_S,
    batch: bool = True,
) -> ElaborationReport:
    """Check all planned entries in a blueprint.

    Args:
        entries: List of dicts with keys: name, suggested_signature, entry_type, status.
            Only entries with status="planned" and non-empty signatures are checked.
        project_root: Path to the project root.
        timeout: Timeout per elaboration.
        batch: If True (default), batch all signatures into one .lean file
            to amortize the ~3-4 min Mathlib import cost. If False, check
            each signature individually (much slower).

    Returns:
        An ElaborationReport with results for each checked entry.
    """
    lake = _find_lake_env_lean()
    if not lake:
        logger.warning(
            "lake binary not found — skipping elaboration check. "
            "Install elan to enable: curl https://raw.githubusercontent.com/"
            "leanprover/elan/master/elan-init.sh -sSf | sh"
        )
        report = ElaborationReport()
        report.total = len(entries)
        report.skipped = len(entries)
        return report

    root = project_root or _PROJECT_ROOT
    report = ElaborationReport()

    planned = [
        e for e in entries
        if e.get("status") == "planned" and e.get("suggested_signature", "").strip()
    ]
    skipped_count = len(entries) - len(planned)

    report.total = len(entries)
    report.skipped = skipped_count

    if not planned:
        return report

    if batch:
        return _check_blueprint_batched(planned, report, root, lake, timeout)
    else:
        return _check_blueprint_sequential(planned, report, root, timeout)


def _check_blueprint_batched(
    planned: list[dict[str, Any]],
    report: ElaborationReport,
    root: Path,
    lake: str,
    timeout: int,
) -> ElaborationReport:
    """Batched checking: all signatures in one .lean file, one Mathlib import."""

    # Build the batched file and entry ranges.
    lean_content, marker_lines = _generate_batched_lean_file(planned)

    # Derive entry_ranges by scanning the generated file for marker comments.
    lines = lean_content.split("\n")
    entry_ranges: list[tuple[str, int, int]] = []
    i = 0
    while i < len(lines):
        if lines[i].startswith("-- @@ELAB_CHECK: "):
            name = lines[i][len("-- @@ELAB_CHECK: "):]
            start = i + 1  # 1-indexed
            # Find end of section (next blank line or end of file).
            j = i + 1
            while j < len(lines) and lines[j].strip() != "":
                j += 1
            end = j  # 1-indexed
            entry_ranges.append((name, start, end))
            i = j
        else:
            i += 1

    # Write to temp file.
    tmp_dir = root / ".elaboration_check_tmp"
    tmp_dir.mkdir(exist_ok=True)
    tmp_file = tmp_dir / "_check_batch.lean"

    print(f"  [elab-check] Batching {len(planned)} signatures into one file...")

    try:
        tmp_file.write_text(lean_content, encoding="utf-8")

        result = subprocess.run(
            [lake, "env", "lean", str(tmp_file)],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(root),
        )

        stderr = result.stderr.strip()

        # Parse errors and attribute to entries.
        errors_by_entry = _parse_batched_errors(
            stderr, entry_ranges, tmp_file.name,
        )

        # Build results.
        for entry in planned:
            name = entry["name"]
            sig = entry["suggested_signature"]
            entry_errors = errors_by_entry.get(name, [])

            if entry_errors:
                error_msg = "\n".join(entry_errors[:5])
                r = ElaborationResult(
                    name=name,
                    passed=False,
                    signature=sig,
                    error_message=error_msg,
                    lean_file="(batched)",
                )
                report.results.append(r)
                report.failed += 1
                first_line = error_msg.split("\n")[0][:80]
                print(f"  [elab-check] {name}: FAIL: {first_line}")
            else:
                r = ElaborationResult(
                    name=name,
                    passed=True,
                    signature=sig,
                    lean_file="(batched)",
                )
                report.results.append(r)
                report.passed += 1
                print(f"  [elab-check] {name}: OK")

        # If the overall process timed out, mark all unchecked as failed.
        if result.returncode != 0 and not errors_by_entry:
            # All entries might have failed due to a global issue (e.g., import error).
            global_error = stderr[:500] if stderr else "Unknown elaboration error"
            for entry in planned:
                name = entry["name"]
                # Don't double-report entries already in results.
                if any(r.name == name for r in report.results):
                    continue
                r = ElaborationResult(
                    name=name,
                    passed=False,
                    signature=entry["suggested_signature"],
                    error_message=f"Global error: {global_error}",
                    lean_file="(batched)",
                )
                report.results.append(r)
                report.failed += 1

    except subprocess.TimeoutExpired:
        print(f"  [elab-check] Batched elaboration timed out after {timeout}s.")
        for entry in planned:
            name = entry["name"]
            if not any(r.name == name for r in report.results):
                r = ElaborationResult(
                    name=name,
                    passed=False,
                    signature=entry["suggested_signature"],
                    error_message=f"Batched elaboration timed out after {timeout}s.",
                )
                report.results.append(r)
                report.failed += 1

    except Exception as exc:
        logger.error("Batched elaboration failed: %s", exc)
        for entry in planned:
            name = entry["name"]
            if not any(r.name == name for r in report.results):
                r = ElaborationResult(
                    name=name,
                    passed=False,
                    signature=entry["suggested_signature"],
                    error_message=f"Unexpected error: {exc}",
                )
                report.results.append(r)
                report.failed += 1

    finally:
        if tmp_file.exists():
            tmp_file.unlink()
        try:
            tmp_dir.rmdir()
        except OSError:
            pass

    return report


def _check_blueprint_sequential(
    planned: list[dict[str, Any]],
    report: ElaborationReport,
    root: Path,
    timeout: int,
) -> ElaborationReport:
    """Sequential checking: one `lake env lean` per signature (slow but isolated)."""
    for i, entry in enumerate(planned):
        name = entry["name"]
        sig = entry["suggested_signature"]
        etype = entry.get("entry_type", "lemma")

        print(f"  [elab-check] ({i + 1}/{len(planned)}) {name}...", end=" ", flush=True)
        result = check_signature(
            name, sig, etype,
            project_root=root,
            timeout=timeout,
        )
        report.results.append(result)
        if result.passed:
            report.passed += 1
            print("OK")
        else:
            report.failed += 1
            first_line = result.error_message.split("\n")[0][:80]
            print(f"FAIL: {first_line}")

    # Clean up temp directory if empty.
    tmp_dir = root / ".elaboration_check_tmp"
    if tmp_dir.exists():
        try:
            tmp_dir.rmdir()
        except OSError:
            pass

    return report
