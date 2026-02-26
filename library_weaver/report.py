"""
Report Generator — produces human-readable and machine-readable run summaries.

Generates two artifacts:
  1. WEAVE_REPORT.md  — markdown summary for human review
  2. weave_report.json — structured data for tooling / resume

Both are written to the run directory and updated incrementally (the JSON
report is written after each entry for crash safety).
"""

from __future__ import annotations

import json
from pathlib import Path

from library_weaver.models import WeaveResult


def write_json_report(result: WeaveResult, run_dir: Path) -> Path:
    """Write (or overwrite) the JSON report. Returns the file path.

    Called after every entry for crash safety, and once more at the
    end of the run with final timing.
    """
    report_path = run_dir / "weave_report.json"
    report_path.write_text(
        json.dumps(result.to_dict(), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return report_path


def write_markdown_report(result: WeaveResult, run_dir: Path) -> Path:
    """Write the final markdown report. Returns the file path."""
    report_path = run_dir / "WEAVE_REPORT.md"
    report_path.write_text(
        _render_markdown(result),
        encoding="utf-8",
    )
    return report_path


def _render_markdown(result: WeaveResult) -> str:
    """Render a WeaveResult as a markdown document."""
    lines: list[str] = []

    lines.append(f"# Weave Report: {result.theme}")
    lines.append("")
    lines.append(f"Run ID: `{result.run_id}`")
    lines.append(f"Blueprint: `{result.blueprint_path}`")
    lines.append(f"Started: {result.started}")
    lines.append(f"Finished: {result.finished}")
    lines.append(f"Duration: {_format_duration(result.duration_seconds)}")
    lines.append("")

    # Summary table
    lines.append("## Summary")
    lines.append("")
    lines.append("| Status  | Count |")
    lines.append("|---------|-------|")
    lines.append(f"| Done    | {result.done_count}     |")
    lines.append(f"| Failed  | {result.failed_count}     |")
    lines.append(f"| Skipped | {result.skipped_count}     |")
    lines.append(f"| Total   | {result.total_planned}    |")
    lines.append("")

    # Per-entry results
    lines.append("## Results by Entry")
    lines.append("")

    for entry in result.entry_results:
        status_upper = entry.status.upper()
        lines.append(f"### {entry.name} — {status_upper}")
        lines.append(f"- Target: `{entry.target_file}`")
        lines.append(f"- Difficulty: {entry.difficulty}")

        if entry.status == "done":
            lines.append(
                f"- Duration: {_format_duration(entry.duration_seconds)}"
            )

        if entry.status == "failed":
            lines.append(
                f"- Duration: {_format_duration(entry.duration_seconds)}"
            )
            if entry.error_message:
                lines.append(f"- Error: {entry.error_message}")

        if entry.status == "skipped" and entry.skip_reason:
            lines.append(f"- Reason: {entry.skip_reason}")

        lines.append("")

    return "\n".join(lines)


def _format_duration(seconds: float) -> str:
    """Format seconds into a human-readable duration string."""
    if seconds < 1.0:
        return "<1s"
    if seconds < 60:
        return f"{seconds:.0f}s"
    minutes = int(seconds // 60)
    remaining = int(seconds % 60)
    if minutes < 60:
        return f"{minutes}m {remaining:02d}s"
    hours = minutes // 60
    remaining_min = minutes % 60
    return f"{hours}h {remaining_min:02d}m"
