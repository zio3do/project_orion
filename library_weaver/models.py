"""
Data models for the Library Weaver orchestration pipeline.

Defines the structured types that flow through the weaver:
  Blueprint Loader → DAG Walker → Proof Loop → Report Generator

All models are frozen dataclasses (where possible) with JSON round-tripping
support via to_dict() / from_dict(). No model contains business logic —
they are pure data carriers.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------------
# Input models (derived from blueprint)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PlannedEntry:
    """A blueprint entry to be proved by the Proof Oracle.

    Represents a single definition or lemma that needs a verified Lean proof.
    Entries are processed in topological order (by order_index).
    """
    name: str
    entry_type: str          # "definition" or "lemma"
    target_file: str         # e.g. "Orion/GradedOrderCombinatorics/LevelSets.lean"
    target_namespace: str    # e.g. "Orion.GradedOrderCombinatorics"
    difficulty: str          # "easy", "medium", "hard"
    layer: str               # e.g. "Layer 1: Level Sets and Basic Properties"
    depends_on: tuple[str, ...] = ()  # Internal deps (other planned entry names)
    spec_file: str = ""      # Filename in lemma_specs/, e.g. "level_mem_iff.json"
    order_index: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "entry_type": self.entry_type,
            "target_file": self.target_file,
            "target_namespace": self.target_namespace,
            "difficulty": self.difficulty,
            "layer": self.layer,
            "depends_on": list(self.depends_on),
            "spec_file": self.spec_file,
            "order_index": self.order_index,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> PlannedEntry:
        return cls(
            name=data["name"],
            entry_type=data["entry_type"],
            target_file=data["target_file"],
            target_namespace=data["target_namespace"],
            difficulty=data.get("difficulty", "easy"),
            layer=data.get("layer", ""),
            depends_on=tuple(data.get("depends_on", [])),
            spec_file=data.get("spec_file", ""),
            order_index=data.get("order_index", 0),
        )


@dataclass(frozen=True)
class ExistingEntry:
    """A blueprint entry that already exists in Mathlib (no proof needed).

    Its definition is seeded into the target file so downstream planned
    entries in the same file can reference it.
    """
    name: str
    target_file: str
    target_namespace: str
    suggested_signature: str   # Complete def to write into the file
    mathlib_reference: str     # e.g. "Erdos1043.levelSet"
    layer: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "target_file": self.target_file,
            "target_namespace": self.target_namespace,
            "suggested_signature": self.suggested_signature,
            "mathlib_reference": self.mathlib_reference,
            "layer": self.layer,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ExistingEntry:
        return cls(
            name=data["name"],
            target_file=data["target_file"],
            target_namespace=data["target_namespace"],
            suggested_signature=data["suggested_signature"],
            mathlib_reference=data.get("mathlib_reference", ""),
            layer=data.get("layer", ""),
        )


# ---------------------------------------------------------------------------
# Result models (produced during the weave)
# ---------------------------------------------------------------------------

@dataclass
class EntryResult:
    """Outcome of processing one planned entry.

    Mutable because fields are populated incrementally as the entry
    is processed (start time set first, then status and duration after).
    """
    name: str
    status: str = "pending"      # "pending", "done", "failed", "skipped"
    target_file: str = ""
    difficulty: str = ""
    duration_seconds: float = 0.0
    skip_reason: str = ""        # If skipped, why
    error_message: str = ""      # If failed due to exception, the error detail

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "name": self.name,
            "status": self.status,
            "target_file": self.target_file,
            "difficulty": self.difficulty,
            "duration_seconds": self.duration_seconds,
        }
        if self.skip_reason:
            d["skip_reason"] = self.skip_reason
        if self.error_message:
            d["error_message"] = self.error_message
        return d

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> EntryResult:
        return cls(
            name=data["name"],
            status=data.get("status", "pending"),
            target_file=data.get("target_file", ""),
            difficulty=data.get("difficulty", ""),
            duration_seconds=data.get("duration_seconds", 0.0),
            skip_reason=data.get("skip_reason", ""),
            error_message=data.get("error_message", ""),
        )


# ---------------------------------------------------------------------------
# Aggregate models
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class WeavePlan:
    """The execution plan derived from a blueprint.

    Produced by the loader, consumed by the weaver core.
    """
    theme: str
    entries: tuple[PlannedEntry, ...]       # Planned entries in topo order
    existing_entries: tuple[ExistingEntry, ...]
    dag: dict[str, tuple[str, ...]]         # name → internal dependency names
    target_files: dict[str, list[str]]      # target_file → list of entry names
    spec_dir: Path
    blueprint_path: Path

    def to_dict(self) -> dict[str, Any]:
        return {
            "theme": self.theme,
            "entries": [e.to_dict() for e in self.entries],
            "existing_entries": [e.to_dict() for e in self.existing_entries],
            "dag": {k: list(v) for k, v in self.dag.items()},
            "target_files": self.target_files,
            "spec_dir": str(self.spec_dir),
            "blueprint_path": str(self.blueprint_path),
        }


@dataclass
class WeaveResult:
    """Aggregate outcome of a weave run.

    Mutable because entry_results are appended incrementally.
    """
    run_id: str
    theme: str
    blueprint_path: str
    started: str = ""            # ISO 8601
    finished: str = ""           # ISO 8601
    duration_seconds: float = 0.0
    entry_results: list[EntryResult] = field(default_factory=list)

    @property
    def done_count(self) -> int:
        return sum(1 for r in self.entry_results if r.status == "done")

    @property
    def failed_count(self) -> int:
        return sum(1 for r in self.entry_results if r.status == "failed")

    @property
    def skipped_count(self) -> int:
        return sum(1 for r in self.entry_results if r.status == "skipped")

    @property
    def total_planned(self) -> int:
        return len(self.entry_results)

    def to_dict(self) -> dict[str, Any]:
        return {
            "run_id": self.run_id,
            "theme": self.theme,
            "blueprint_path": self.blueprint_path,
            "started": self.started,
            "finished": self.finished,
            "duration_seconds": self.duration_seconds,
            "summary": {
                "total_planned": self.total_planned,
                "done": self.done_count,
                "failed": self.failed_count,
                "skipped": self.skipped_count,
            },
            "entries": [r.to_dict() for r in self.entry_results],
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> WeaveResult:
        result = cls(
            run_id=data["run_id"],
            theme=data["theme"],
            blueprint_path=data["blueprint_path"],
            started=data.get("started", ""),
            finished=data.get("finished", ""),
            duration_seconds=data.get("duration_seconds", 0.0),
        )
        for entry_data in data.get("entries", []):
            result.entry_results.append(EntryResult.from_dict(entry_data))
        return result
