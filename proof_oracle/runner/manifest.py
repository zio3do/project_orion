"""
manifest.py — MANIFEST.md reader/writer for the Proof Oracle.

Responsibility: Track per-lemma attempt history in a human-readable,
git-diffable markdown file. Each lemma gets an entry with status, attempt
count, error history, and notes.

The MANIFEST serves two purposes:
  1. Human inspection — see at a glance what worked, what's stuck, and why.
  2. Retry context — the orchestrator reads previous errors to build better
     retry prompts.

Format: see Section 4.4 of proof_oracle_design.md for the full specification.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path


@dataclass
class LemmaEntry:
    """One lemma's record in the MANIFEST."""

    name: str
    status: str = "todo"  # "todo", "in_progress", "done", "failed"
    target_file: str = ""
    attempts_used: int = 0
    attempts_max: int = 10
    informal_statement: str = ""
    notes: str = ""
    errors: str = ""
    cost_usd: float = 0.0  # Total cost: pre-search + all session costs


class Manifest:
    """
    Read and write MANIFEST.md files.

    The manifest is a flat list of lemma entries with metadata header.
    We parse the markdown structure on read and regenerate it on write.
    This is intentionally simple — no YAML/TOML dependency, just markdown.
    """

    def __init__(
        self,
        path: Path,
        pocket_name: str = "",
        source: str = "",
    ):
        self.path = path
        self.pocket_name = pocket_name
        self.source = source
        self.started: str = ""
        self.entries: dict[str, LemmaEntry] = {}

    def get_entry(self, lemma_name: str) -> LemmaEntry | None:
        """Get a lemma entry by name, or None if not found."""
        return self.entries.get(lemma_name)

    def upsert_entry(self, entry: LemmaEntry) -> None:
        """Insert or update a lemma entry."""
        self.entries[entry.name] = entry

    def write(self) -> None:
        """Write the manifest to disk as markdown."""
        lines = []

        # Header
        lines.append(f"# Pocket: {self.pocket_name}")
        if self.source:
            lines.append(f"# Source: {self.source}")
        if not self.started:
            self.started = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        lines.append(f"# Started: {self.started}")
        lines.append("")

        # Entries
        for entry in self.entries.values():
            lines.append(f"## Lemma: {entry.name}")
            lines.append(f"- status: {entry.status}")
            if entry.target_file:
                lines.append(f"- file: {entry.target_file}")
            lines.append(f"- attempts: {entry.attempts_used}/{entry.attempts_max}")
            if entry.cost_usd > 0:
                lines.append(f"- cost: ${entry.cost_usd:.4f}")
            if entry.informal_statement:
                lines.append(f"- statement: {entry.informal_statement}")
            if entry.notes:
                lines.append(f"- notes: {entry.notes}")
            if entry.errors:
                lines.append(f"- errors: |")
                for error_line in entry.errors.strip().splitlines():
                    lines.append(f"    {error_line}")
            lines.append("")

        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text("\n".join(lines), encoding="utf-8")

    @classmethod
    def load(cls, path: Path) -> Manifest:
        """
        Load a manifest from disk. If the file doesn't exist, return an
        empty manifest bound to that path.
        """
        manifest = cls(path=path)

        if not path.exists():
            return manifest

        content = path.read_text(encoding="utf-8")
        lines = content.splitlines()

        # Parse header
        for line in lines:
            if line.startswith("# Pocket:"):
                manifest.pocket_name = line.split(":", 1)[1].strip()
            elif line.startswith("# Source:"):
                manifest.source = line.split(":", 1)[1].strip()
            elif line.startswith("# Started:"):
                manifest.started = line.split(":", 1)[1].strip()
            elif line.startswith("## Lemma:"):
                break

        # Parse entries
        current_entry: LemmaEntry | None = None
        in_errors_block = False

        for line in lines:
            # New lemma section
            lemma_match = re.match(r"^## Lemma:\s*(.+)$", line)
            if lemma_match:
                if current_entry is not None:
                    manifest.entries[current_entry.name] = current_entry
                current_entry = LemmaEntry(name=lemma_match.group(1).strip())
                in_errors_block = False
                continue

            if current_entry is None:
                continue

            # Inside an errors block (indented lines)
            if in_errors_block:
                if line.startswith("    "):
                    current_entry.errors += line.strip() + "\n"
                    continue
                elif line.startswith("- ") or line.startswith("## "):
                    in_errors_block = False
                    # Fall through to parse this line normally
                elif line.strip() == "":
                    in_errors_block = False
                    continue
                else:
                    continue

            # Parse key-value fields
            if line.startswith("- status:"):
                current_entry.status = line.split(":", 1)[1].strip()
            elif line.startswith("- file:"):
                current_entry.target_file = line.split(":", 1)[1].strip()
            elif line.startswith("- attempts:"):
                attempts_str = line.split(":", 1)[1].strip()
                parts = attempts_str.split("/")
                if len(parts) == 2:
                    try:
                        current_entry.attempts_used = int(parts[0])
                        current_entry.attempts_max = int(parts[1])
                    except ValueError:
                        pass
            elif line.startswith("- cost:"):
                cost_str = line.split(":", 1)[1].strip().lstrip("$")
                try:
                    current_entry.cost_usd = float(cost_str)
                except ValueError:
                    pass
            elif line.startswith("- statement:"):
                current_entry.informal_statement = line.split(":", 1)[1].strip()
            elif line.startswith("- notes:"):
                current_entry.notes = line.split(":", 1)[1].strip()
            elif line.startswith("- errors:"):
                in_errors_block = True
                # The value after "errors:" might be "|" (block) or inline
                val = line.split(":", 1)[1].strip()
                if val and val != "|":
                    current_entry.errors = val + "\n"

        # Don't forget the last entry
        if current_entry is not None:
            manifest.entries[current_entry.name] = current_entry

        return manifest
