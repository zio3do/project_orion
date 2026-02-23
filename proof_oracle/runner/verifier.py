"""
verifier.py — Hard verification gate for the Proof Oracle.

Responsibility: Run `lake env lean <file>` and determine if a proof is valid.
This is the single source of truth. The agent's self-report is never trusted.

Invariants (non-negotiable):
  1. No proof accepted without passing `lake env lean`.
  2. Any `sorry` in compiler output → FAIL (gaps must be visible).
  3. Any `axiom` declaration in the file → FAIL (prevents silent unsoundness).
  4. Zero compiler errors required for PASS.

Usage:
  result = verify(Path("Orion/FiniteDifference.lean"), Path("."))
  if result.passed:
      print("Proof verified!")
  else:
      print(f"Failed: {result.errors}")
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

# Timeout for lake env lean (seconds). First invocation may be slow due to
# Mathlib import compilation; subsequent invocations use cache.
VERIFICATION_TIMEOUT_SECONDS = 600


@dataclass
class VerificationResult:
    """Result of running the verification gate on a Lean file."""

    passed: bool
    errors: list[str] = field(default_factory=list)
    has_sorry: bool = False
    has_axiom: bool = False
    raw_stdout: str = ""
    raw_stderr: str = ""
    timed_out: bool = False

    def summary(self) -> str:
        """One-line summary for MANIFEST and logs."""
        if self.timed_out:
            return "TIMEOUT: verification exceeded time limit"
        if self.passed:
            return "PASS: zero errors, no sorry, no axiom"
        parts = []
        if self.has_sorry:
            parts.append("sorry detected")
        if self.has_axiom:
            parts.append("axiom declaration detected")
        if self.errors:
            parts.append(f"{len(self.errors)} compiler error(s)")
        return "FAIL: " + "; ".join(parts)


def _scan_for_axiom_declarations(lean_file: Path) -> bool:
    """
    Scan a .lean file for `axiom` declarations.

    We look for top-level `axiom` keywords that introduce unsound assumptions.
    This is distinct from Lean's built-in axioms (like propext) — we scan the
    user-written file content for explicit axiom declarations.

    Pattern: line starts with `axiom` followed by whitespace and an identifier.
    This avoids false positives from comments or strings containing the word.
    """
    try:
        content = lean_file.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        # If we can't read the file, flag it as suspicious
        return True

    # Match `axiom <identifier>` at the start of a line (possibly with leading whitespace)
    # Also match `noncomputable axiom` and `private axiom` variants
    axiom_pattern = re.compile(
        r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\s+\w+",
        re.MULTILINE,
    )

    for match in axiom_pattern.finditer(content):
        # Check this isn't inside a comment block
        line_start = content.rfind("\n", 0, match.start()) + 1
        line_prefix = content[line_start : match.start()]

        # Skip if preceded by -- (line comment)
        if "--" in line_prefix:
            continue

        # Check if we're inside a /- -/ block comment
        # Count unmatched /- before this position
        before = content[: match.start()]
        open_comments = len(re.findall(r"/-", before)) - len(re.findall(r"-/", before))
        if open_comments > 0:
            continue

        return True

    return False


def _parse_lean_errors(output: str) -> list[str]:
    """
    Parse Lean compiler error messages from compiler output.

    Lean error format: `<file>:<line>:<col>: error: <message>`
    We collect the full error lines. Warnings are not treated as errors.

    Note: Lean may emit diagnostics to either stdout or stderr depending on
    the message type, so callers should pass the combined output.
    """
    errors = []
    for line in output.splitlines():
        # Lean errors have the pattern: path:line:col: error: message
        if ": error:" in line:
            errors.append(line.strip())
    return errors


def _check_sorry_in_output(output: str) -> bool:
    """
    Check if the compiler output indicates sorry usage.

    Lean 4 reports: "declaration uses `sorry`" (with backticks) as a warning.
    This may appear on stdout or stderr depending on the Lean version.
    We also check for "unsolved goals" which indicates incomplete proofs.

    We normalize the check to be quote-style-agnostic: we look for the
    substring "declaration uses" + "sorry" on the same line.
    """
    sorry_indicators = [
        "declaration uses 'sorry'",  # single quotes (older format)
        "declaration uses `sorry`",  # backticks (Lean 4 current format)
        "declaration uses \u2018sorry\u2019",  # unicode quotes (just in case)
        "unsolved goals",
    ]
    output_lower = output.lower()
    return any(indicator.lower() in output_lower for indicator in sorry_indicators)


def verify(
    lean_file: Path,
    project_root: Path,
    timeout: int = VERIFICATION_TIMEOUT_SECONDS,
) -> VerificationResult:
    """
    Run the verification gate on a Lean file.

    Steps:
      1. Run `lake env lean <file>` in the project root.
      2. Parse stderr for compiler errors.
      3. Check for sorry usage in compiler output.
      4. Scan the source file for axiom declarations.
      5. Return pass/fail with details.

    Args:
        lean_file: Path to the .lean file (relative to project_root or absolute).
        project_root: Path to the Lean project root (contains lakefile.toml).
        timeout: Maximum seconds to wait for compilation.

    Returns:
        VerificationResult with pass/fail status and details.
    """
    # Resolve paths
    if not lean_file.is_absolute():
        absolute_lean_file = project_root / lean_file
    else:
        absolute_lean_file = lean_file

    if not absolute_lean_file.exists():
        return VerificationResult(
            passed=False,
            errors=[f"File not found: {lean_file}"],
        )

    if not (project_root / "lakefile.toml").exists():
        return VerificationResult(
            passed=False,
            errors=[f"No lakefile.toml in project root: {project_root}"],
        )

    # Run lake env lean
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=str(project_root),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return VerificationResult(
            passed=False,
            errors=[f"Compilation timed out after {timeout}s"],
            timed_out=True,
        )
    except FileNotFoundError:
        return VerificationResult(
            passed=False,
            errors=["'lake' command not found — is Lean/Lake installed and on PATH?"],
        )

    # Parse results — check both stdout and stderr since Lean routes
    # different diagnostic types to different streams
    combined_output = result.stdout + "\n" + result.stderr
    errors = _parse_lean_errors(combined_output)
    has_sorry = _check_sorry_in_output(combined_output)
    has_axiom = _scan_for_axiom_declarations(absolute_lean_file)

    passed = len(errors) == 0 and not has_sorry and not has_axiom

    return VerificationResult(
        passed=passed,
        errors=errors,
        has_sorry=has_sorry,
        has_axiom=has_axiom,
        raw_stdout=result.stdout,
        raw_stderr=result.stderr,
    )
