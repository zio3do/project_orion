"""
orchestrator.py — Top-level entry point for the Proof Oracle.

Responsibility: Read a single lemma specification, run the proof loop
(prompt → Claude Code → verify → retry), and produce a verified Lean file
with attempt history in MANIFEST.md.

This is the "Python runner" from the design doc (Section 4.1). It does pure
deterministic work: read files, spawn subprocesses, check return values,
write status updates. No reasoning, no LLM calls for orchestration.

Usage:
  python -m proof_oracle.runner.orchestrator lemma_specs/fwdDiff_linear.json

Or programmatically:
  from proof_oracle.runner.orchestrator import run_lemma
  result = run_lemma(Path("lemma_specs/fwdDiff_linear.json"))
"""

from __future__ import annotations

import json
import logging
import sys
from datetime import datetime, timezone
from pathlib import Path

from .manifest import LemmaEntry, Manifest
from .pre_search import PreSearchResult, run_pre_search
from .prompt_builder import LemmaSpec, build_prompt
from .session import SessionResult, run_session
from .verifier import verify

logger = logging.getLogger(__name__)

# Resolve paths relative to the proof_oracle package
PROOF_ORACLE_DIR = Path(__file__).resolve().parent.parent
PROJECT_ROOT = PROOF_ORACLE_DIR.parent
PROMPTS_DIR = PROOF_ORACLE_DIR / "prompts"
RUNS_DIR = PROOF_ORACLE_DIR / "runs"


class CreditExhaustedError(RuntimeError):
    """Raised when the Claude API credit balance is exhausted.

    This is an infrastructure error, not a proof failure. When raised from
    ``run_lemma``, the caller (Library Weaver) should halt the entire run
    rather than attempting subsequent entries — they will all fail the same
    way, wasting budget and wall-clock time.
    """


# Phrases indicating Claude API credit exhaustion in session output.
# When detected, retrying is pointless — all subsequent attempts will fail.
_CREDIT_EXHAUSTION_PHRASES = [
    "credit balance is too low",
    "insufficient_credits",
    "billing_error",
]


def _is_credit_exhausted(session_result: SessionResult) -> bool:
    """
    Check if a Claude Code session failed due to API credit exhaustion.

    Detects the "Credit balance is too low" message that Claude CLI returns
    when the account has insufficient credits. This check inspects both stdout
    and stderr since the error can appear in either stream depending on how
    far the session progressed before credits ran out.

    Returns True if credit exhaustion is detected.
    """
    combined = (session_result.raw_output + session_result.raw_stderr).lower()
    return any(phrase in combined for phrase in _CREDIT_EXHAUSTION_PHRASES)


def _load_lemma_spec(spec_path: Path) -> LemmaSpec:
    """Load and validate a lemma spec from a JSON file."""
    if not spec_path.exists():
        raise FileNotFoundError(f"Lemma spec not found: {spec_path}")

    with open(spec_path, encoding="utf-8") as f:
        data = json.load(f)

    required_fields = [
        "lemma_name",
        "target_file",
        "informal_statement",
        "suggested_signature",
    ]
    for field in required_fields:
        if field not in data:
            raise ValueError(
                f"Lemma spec missing required field '{field}': {spec_path}"
            )

    return LemmaSpec.from_dict(data)


def _create_run_id(lemma_name: str) -> str:
    """Create a unique run ID for logging."""
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"{lemma_name}_{timestamp}"


def run_lemma(
    spec_path: Path,
    project_root: Path | None = None,
    manifest_path: Path | None = None,
) -> bool:
    """
    Run the full proof loop for a single lemma specification.

    Steps:
      1. Load the lemma spec from JSON.
      2. Initialize/load the MANIFEST.md entry.
      3. For each attempt up to the budget:
         a. Build the proof prompt (with error context if retrying).
         b. Spawn a fresh Claude Code session.
         c. Run the verification gate on the target file.
         d. If verified, mark done and return True.
         e. If failed, record errors and retry.
      4. If budget exhausted, mark failed and return False.

    Args:
        spec_path: Path to the lemma_spec.json file.
        project_root: Lean project root. Defaults to PROJECT_ROOT.
        manifest_path: Path to MANIFEST.md. Defaults to runs/<run_id>/MANIFEST.md.

    Returns:
        True if the lemma was successfully verified, False otherwise.
    """
    if project_root is None:
        project_root = PROJECT_ROOT

    # Load the lemma spec
    spec = _load_lemma_spec(spec_path)
    logger.info("Loaded lemma spec: %s", spec.lemma_name)
    logger.info("  Target file: %s", spec.target_file)
    logger.info("  Difficulty: %s", spec.difficulty)
    logger.info("  Budget: %d attempts", spec.attempt_budget)

    # Create run directory
    run_id = _create_run_id(spec.lemma_name)
    run_dir = RUNS_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    log_dir = run_dir / "session_logs"

    # Initialize manifest
    if manifest_path is None:
        manifest_path = run_dir / "MANIFEST.md"

    manifest = Manifest.load(manifest_path)
    if not manifest.pocket_name:
        manifest.pocket_name = f"Single lemma: {spec.lemma_name}"
    manifest.source = str(spec_path)

    # Create or update the lemma entry
    entry = manifest.get_entry(spec.lemma_name) or LemmaEntry(name=spec.lemma_name)
    entry.status = "in_progress"
    entry.target_file = spec.target_file
    entry.attempts_max = spec.attempt_budget
    entry.informal_statement = spec.informal_statement
    manifest.upsert_entry(entry)
    manifest.write()

    # Proof loop
    previous_errors = ""
    pre_search_context = ""

    # Pre-search: generate relevant Mathlib context before the proof loop.
    # This runs once per lemma, not per attempt. The context is injected into
    # every attempt's prompt so the agent starts warm.
    try:
        logger.info("Running pre-search for %s...", spec.lemma_name)
        pre_search_result: PreSearchResult = run_pre_search(
            lemma_name=spec.lemma_name,
            informal_statement=spec.informal_statement,
            suggested_signature=spec.suggested_signature,
            depends_on=spec.depends_on,
            project_root=project_root,
        )
        pre_search_context = pre_search_result.context_block
        logger.info(
            "Pre-search complete: %d declarations found, cost=$%.4f",
            pre_search_result.declarations_found,
            pre_search_result.cost_usd,
        )
        entry.cost_usd += pre_search_result.cost_usd
    except Exception as e:
        logger.warning(
            "Pre-search failed (non-fatal, continuing without context): %s", e
        )
        pre_search_result = None  # type: ignore[assignment]

    for attempt in range(1, spec.attempt_budget + 1):
        logger.info(
            "=== Attempt %d/%d for %s ===",
            attempt,
            spec.attempt_budget,
            spec.lemma_name,
        )

        # Build the prompt
        prompt = build_prompt(
            spec=spec,
            prompts_dir=PROMPTS_DIR,
            project_root=project_root,
            pre_search_context=pre_search_context,
            previous_errors=previous_errors,
            attempt_number=attempt,
        )

        # Run Claude Code session
        session_result = run_session(
            prompt=prompt,
            project_root=project_root,
            log_dir=log_dir,
            attempt_number=attempt,
        )

        logger.info(
            "Session ended: end_reason=%s, duration=%.1fs, cost=$%.4f",
            session_result.end_reason,
            session_result.duration_seconds,
            session_result.cost_usd,
        )

        # Accumulate session cost
        entry.cost_usd += session_result.cost_usd

        # Check for unrecoverable session errors
        if session_result.end_reason == "ERROR":
            logger.error(
                "Claude Code session reported ERROR. stderr: %s",
                session_result.raw_stderr[:500],
            )
            entry.notes = f"Attempt {attempt}: session error"
            entry.errors = session_result.raw_stderr[:1000]
            entry.attempts_used = attempt
            manifest.upsert_entry(entry)
            manifest.write()

            # Don't retry on session-level errors (e.g., CLI not found)
            if "not found" in session_result.raw_stderr.lower():
                logger.error("Claude Code CLI not available. Aborting.")
                entry.status = "failed"
                manifest.upsert_entry(entry)
                manifest.write()
                return False

            # Other session errors: continue to retry
            previous_errors = session_result.raw_stderr
            continue

        # Check for credit exhaustion — abort immediately, no retry
        if _is_credit_exhausted(session_result):
            logger.error(
                "Claude API credit balance exhausted. "
                "Aborting proof loop — retrying would waste budget."
            )
            entry.status = "failed"
            entry.attempts_used = attempt
            entry.notes = (
                f"Credit balance exhausted on attempt {attempt}. "
                f"No further attempts possible until credits are replenished."
            )
            entry.errors = "Credit balance is too low"
            manifest.upsert_entry(entry)
            manifest.write()
            raise CreditExhaustedError(
                f"Claude API credits exhausted during {spec.lemma_name} "
                f"(attempt {attempt}/{spec.attempt_budget}). "
                f"Replenish credits before retrying."
            )

        # Run verification gate
        lean_file = Path(spec.target_file)
        logger.info("Running verification gate on %s", lean_file)

        verification = verify(lean_file, project_root, lemma_name=spec.lemma_name)
        logger.info("Verification: %s", verification.summary())

        if verification.passed:
            # Success!
            logger.info(
                "VERIFIED: %s passed verification on attempt %d",
                spec.lemma_name,
                attempt,
            )
            entry.status = "done"
            entry.attempts_used = attempt
            entry.notes = f"Verified on attempt {attempt}. {verification.summary()}"
            entry.errors = ""
            manifest.upsert_entry(entry)
            manifest.write()
            return True

        # Verification failed — prepare for retry
        error_summary = verification.summary()
        error_details = "\n".join(verification.errors) if verification.errors else ""
        if verification.has_sorry:
            error_details += "\n[sorry detected in compilation output]"
        if verification.has_axiom:
            error_details += "\n[axiom declaration detected in source file]"

        previous_errors = (
            f"Verification result: {error_summary}\n\n"
            f"Error details:\n{error_details}\n\n"
            f"Raw compiler output:\n{verification.raw_stderr[:2000]}"
        )

        entry.attempts_used = attempt
        entry.notes = f"Attempt {attempt}: {error_summary}"
        entry.errors = error_details
        manifest.upsert_entry(entry)
        manifest.write()

        logger.info(
            "Attempt %d failed. %d attempts remaining.",
            attempt,
            spec.attempt_budget - attempt,
        )

    # Budget exhausted
    logger.warning(
        "Budget exhausted for %s after %d attempts",
        spec.lemma_name,
        spec.attempt_budget,
    )
    entry.status = "failed"
    entry.notes = (
        f"Budget exhausted after {spec.attempt_budget} attempts. "
        f"Last error: {previous_errors[:200]}"
    )
    manifest.upsert_entry(entry)
    manifest.write()
    return False


def main() -> None:
    """CLI entry point: python -m proof_oracle.runner.orchestrator <spec.json>"""
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )

    if len(sys.argv) < 2:
        print("Usage: python -m proof_oracle.runner.orchestrator <lemma_spec.json>")
        print()
        print("Example:")
        print(
            "  python -m proof_oracle.runner.orchestrator "
            "proof_oracle/lemma_specs/fwdDiff_linear.json"
        )
        sys.exit(1)

    spec_path = Path(sys.argv[1])

    # Allow relative paths from either project root or current directory
    if not spec_path.exists() and not spec_path.is_absolute():
        # Try relative to project root
        alt_path = PROJECT_ROOT / spec_path
        if alt_path.exists():
            spec_path = alt_path

    success = run_lemma(spec_path)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
