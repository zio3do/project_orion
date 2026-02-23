"""
session.py — Claude Code session manager for the Proof Oracle.

Responsibility: Invoke Claude Code in non-interactive mode with a proof prompt,
capture its output, parse the END_REASON sentinel, and save session logs.

Each proof attempt is a fresh Claude Code session (not a continuation).
This is a deliberate design choice: fresh context prevents error-fixing loops
from filling the context window. The retry prompt includes only what matters:
the task + what went wrong last time.

Claude Code invocation:
  claude -p <prompt> --output-format json

The --output-format json flag makes Claude Code return structured JSON output
including the assistant's response text, which we parse for the END_REASON
sentinel.

END_REASON sentinels (from Section 8.3 of the design doc):
  END_REASON:COMPLETE — Agent believes the proof compiles with no sorry.
  END_REASON:LIMIT    — Agent exhausted its context or search budget.
  END_REASON:ERROR    — Agent encountered an unrecoverable error.
"""

from __future__ import annotations

import json
import logging
import os
import re
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

logger = logging.getLogger(__name__)

# Resolve project root (proof_oracle/runner/session.py -> project root)
_PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent

# Regex to extract END_REASON sentinel from agent output.
# The agent may wrap the sentinel in markdown backticks: `END_REASON:COMPLETE`
END_REASON_PATTERN = re.compile(
    r"^\s*`?END_REASON:(COMPLETE|LIMIT|ERROR)`?\s*$", re.MULTILINE
)

# Timeout for a single Claude Code session (seconds).
# Proof sessions can be long due to multiple tool calls.
SESSION_TIMEOUT_SECONDS = 900  # 15 minutes


@dataclass
class SessionResult:
    """Result of a single Claude Code proof session."""

    end_reason: str  # "COMPLETE", "LIMIT", "ERROR", or "UNKNOWN"
    raw_output: str  # Full stdout from claude
    raw_stderr: str  # Full stderr from claude
    exit_code: int
    duration_seconds: float
    timed_out: bool = False
    cost_usd: float = 0.0  # Cost from Claude Code's total_cost_usd field

    @property
    def agent_believes_complete(self) -> bool:
        """Whether the agent reported the proof is done."""
        return self.end_reason == "COMPLETE"


def _parse_end_reason(output: str) -> str:
    """
    Extract the END_REASON sentinel from Claude Code output.

    If the output is JSON (--output-format json), parse it first to get
    the assistant's response text. If it's plain text, search directly.

    Returns one of: "COMPLETE", "LIMIT", "ERROR", "UNKNOWN".
    """
    # Try to parse as JSON first (claude --output-format json)
    text_to_search = output
    try:
        data = json.loads(output)
        # Claude Code JSON output has a "result" field with the response
        if isinstance(data, dict):
            # Try common JSON output structures
            if "result" in data:
                text_to_search = str(data["result"])
            elif "content" in data:
                text_to_search = str(data["content"])
            elif "message" in data:
                text_to_search = str(data["message"])
    except (json.JSONDecodeError, TypeError):
        pass

    match = END_REASON_PATTERN.search(text_to_search)
    if match:
        return match.group(1)

    return "UNKNOWN"


def _parse_cost(output: str) -> float:
    """
    Extract total_cost_usd from Claude Code JSON output.

    Returns 0.0 if the cost cannot be parsed.
    """
    try:
        data = json.loads(output)
        if isinstance(data, dict):
            cost = data.get("total_cost_usd", 0.0)
            if isinstance(cost, (int, float)):
                return float(cost)
    except (json.JSONDecodeError, TypeError):
        pass
    return 0.0


def _save_session_log(
    log_dir: Path,
    attempt_number: int,
    prompt: str,
    result: SessionResult,
) -> Path:
    """Save the session prompt and output to a log file for inspection."""
    log_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    log_file = log_dir / f"attempt_{attempt_number:02d}_{timestamp}.json"

    log_data = {
        "attempt": attempt_number,
        "timestamp": timestamp,
        "end_reason": result.end_reason,
        "exit_code": result.exit_code,
        "duration_seconds": result.duration_seconds,
        "cost_usd": result.cost_usd,
        "timed_out": result.timed_out,
        "prompt": prompt,
        "stdout": result.raw_output,
        "stderr": result.raw_stderr,
    }

    log_file.write_text(
        json.dumps(log_data, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    return log_file


def _build_env(project_root: Path) -> dict[str, str]:
    """
    Build the environment dict for the Claude Code subprocess.

    Loads .env from the project root and maps CLAUDE_API_KEY to
    ANTHROPIC_API_KEY (which is what the claude CLI reads).
    Inherits the current process environment as a base.
    """
    env = os.environ.copy()

    # Load .env file if it exists
    dotenv_path = project_root / ".env"
    if dotenv_path.exists():
        for line in dotenv_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "=" in line:
                key, _, value = line.partition("=")
                env[key.strip()] = value.strip()

    # Map CLAUDE_API_KEY -> ANTHROPIC_API_KEY if the latter isn't already set
    if "ANTHROPIC_API_KEY" not in env and "CLAUDE_API_KEY" in env:
        env["ANTHROPIC_API_KEY"] = env["CLAUDE_API_KEY"]

    return env


def run_session(
    prompt: str,
    project_root: Path,
    log_dir: Path,
    attempt_number: int = 1,
    timeout: int = SESSION_TIMEOUT_SECONDS,
) -> SessionResult:
    """
    Invoke Claude Code with a proof prompt and capture the result.

    Runs: claude -p <prompt> --output-format json
    in the project root directory with bypassPermissions mode.

    Args:
        prompt: The complete proof agent prompt.
        project_root: Working directory for Claude Code (the Lean project root).
        log_dir: Directory to save session logs.
        attempt_number: Which attempt this is (for logging).
        timeout: Maximum seconds to wait for the session.

    Returns:
        SessionResult with end_reason, output, and timing info.
    """
    import time

    start_time = time.monotonic()

    cmd = [
        "claude",
        "-p",
        prompt,
        "--output-format",
        "json",
        "--permission-mode",
        "bypassPermissions",
    ]

    # Build environment with API keys from .env
    env = _build_env(project_root)

    logger.info(
        "Starting Claude Code session (attempt %d), timeout=%ds",
        attempt_number,
        timeout,
    )

    try:
        result = subprocess.run(
            cmd,
            cwd=str(project_root),
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        elapsed = time.monotonic() - start_time

        end_reason = _parse_end_reason(result.stdout)
        cost = _parse_cost(result.stdout)

        session_result = SessionResult(
            end_reason=end_reason,
            raw_output=result.stdout,
            raw_stderr=result.stderr,
            exit_code=result.returncode,
            duration_seconds=elapsed,
            cost_usd=cost,
        )

    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start_time
        logger.warning(
            "Claude Code session timed out after %.1fs (attempt %d)",
            elapsed,
            attempt_number,
        )
        session_result = SessionResult(
            end_reason="LIMIT",
            raw_output="",
            raw_stderr=f"Session timed out after {timeout}s",
            exit_code=-1,
            duration_seconds=elapsed,
            timed_out=True,
        )

    except FileNotFoundError:
        elapsed = time.monotonic() - start_time
        logger.error(
            "Claude Code CLI ('claude') not found. "
            "Install it: https://docs.anthropic.com/en/docs/claude-code"
        )
        session_result = SessionResult(
            end_reason="ERROR",
            raw_output="",
            raw_stderr=(
                "'claude' command not found. "
                "Install Claude Code CLI and ensure it is on your PATH."
            ),
            exit_code=-1,
            duration_seconds=elapsed,
        )

    # Save the session log
    log_path = _save_session_log(log_dir, attempt_number, prompt, session_result)
    logger.info(
        "Session complete: end_reason=%s, duration=%.1fs, log=%s",
        session_result.end_reason,
        session_result.duration_seconds,
        log_path,
    )

    return session_result
