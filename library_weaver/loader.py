"""
Blueprint Loader — parses blueprint.json into a WeavePlan.

Reads the Library Architect's output directory, separates planned entries
from exists_in_mathlib entries, builds the internal dependency graph, and
validates that all spec files exist. The result is a WeavePlan consumed
by the weaver core and all downstream components.

Blueprint JSON structure assumptions:
  - Planned entries have target_file and target_namespace inside their
    nested "lemma_spec" sub-object (not at the top level).
  - exists_in_mathlib entries have NO lemma_spec and NO target_file.
    The loader infers target_file from the first planned entry that
    depends on the existing entry.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from library_weaver.models import ExistingEntry, PlannedEntry, WeavePlan


def load_blueprint(blueprint_dir: Path) -> WeavePlan:
    """Parse a blueprint directory into a WeavePlan.

    Args:
        blueprint_dir: Path to the Library Architect output directory.
            Must contain blueprint.json and lemma_specs/.

    Returns:
        A WeavePlan ready for the weaver core.

    Raises:
        FileNotFoundError: If blueprint.json or lemma_specs/ is missing.
        ValueError: If validation fails (missing deps, missing spec files).
    """
    blueprint_path = blueprint_dir / "blueprint.json"
    spec_dir = blueprint_dir / "lemma_specs"

    if not blueprint_path.exists():
        raise FileNotFoundError(f"Blueprint not found: {blueprint_path}")
    if not spec_dir.is_dir():
        raise FileNotFoundError(f"Spec directory not found: {spec_dir}")

    with open(blueprint_path, "r") as f:
        blueprint = json.load(f)

    theme = blueprint["theme"]
    raw_entries: list[dict[str, Any]] = blueprint["entries"]

    # -----------------------------------------------------------------------
    # Separate planned entries from exists_in_mathlib entries
    # -----------------------------------------------------------------------
    planned_entries: list[PlannedEntry] = []
    existing_entries_raw: list[dict[str, Any]] = []
    planned_names: set[str] = set()

    for raw in raw_entries:
        status = raw.get("status", "planned")

        if status == "planned":
            entry = _parse_planned_entry(raw)
            planned_entries.append(entry)
            planned_names.add(entry.name)

        elif status == "exists_in_mathlib":
            existing_entries_raw.append(raw)

        # Skip any other status (e.g. "skipped")

    # Sort planned entries by order_index (should already be sorted, but
    # enforce it for safety)
    planned_entries.sort(key=lambda e: e.order_index)

    # -----------------------------------------------------------------------
    # Resolve exists_in_mathlib entries: infer target_file from dependents
    # -----------------------------------------------------------------------
    existing_entries = _resolve_existing_entries(
        existing_entries_raw, planned_entries
    )

    # -----------------------------------------------------------------------
    # Build internal dependency graph (only edges between planned entries)
    # -----------------------------------------------------------------------
    dag: dict[str, tuple[str, ...]] = {}
    for entry in planned_entries:
        internal_deps = tuple(d for d in entry.depends_on if d in planned_names)
        dag[entry.name] = internal_deps

    # -----------------------------------------------------------------------
    # Build target_files mapping: target_file → [entry_names]
    # -----------------------------------------------------------------------
    target_files: dict[str, list[str]] = {}
    for entry in planned_entries:
        target_files.setdefault(entry.target_file, []).append(entry.name)

    # Also include existing entries in target_files
    for existing in existing_entries:
        target_files.setdefault(existing.target_file, [])

    # -----------------------------------------------------------------------
    # Validate
    # -----------------------------------------------------------------------
    _validate(planned_entries, planned_names, spec_dir)

    return WeavePlan(
        theme=theme,
        entries=tuple(planned_entries),
        existing_entries=tuple(existing_entries),
        dag=dag,
        target_files=target_files,
        spec_dir=spec_dir,
        blueprint_path=blueprint_path,
    )


def _parse_planned_entry(raw: dict[str, Any]) -> PlannedEntry:
    """Extract a PlannedEntry from a raw blueprint entry dict.

    The target_file and target_namespace are nested inside lemma_spec.
    """
    lemma_spec = raw.get("lemma_spec")
    if lemma_spec is None:
        raise ValueError(
            f"Planned entry '{raw['name']}' is missing 'lemma_spec'. "
            "Cannot determine target_file."
        )

    return PlannedEntry(
        name=raw["name"],
        entry_type=raw.get("entry_type", "lemma"),
        target_file=lemma_spec["target_file"],
        target_namespace=lemma_spec["target_namespace"],
        difficulty=raw.get("difficulty", "easy"),
        layer=raw.get("layer", ""),
        depends_on=tuple(raw.get("depends_on", [])),
        spec_file=f"{raw['name']}.json",
        order_index=raw.get("order_index", 0),
    )


def _resolve_existing_entries(
    existing_raw: list[dict[str, Any]],
    planned: list[PlannedEntry],
) -> list[ExistingEntry]:
    """Build ExistingEntry objects, inferring target_file from planned dependents.

    An exists_in_mathlib entry (like "level") has no lemma_spec and no
    target_file. We infer the target_file by finding the first planned
    entry that depends on it (by order_index) and using that entry's
    target_file.
    """
    result: list[ExistingEntry] = []

    for raw in existing_raw:
        name = raw["name"]

        # Find the first planned entry (by order_index) that depends on this
        first_dependent = _find_first_dependent(name, planned)

        if first_dependent is not None:
            target_file = first_dependent.target_file
            target_namespace = first_dependent.target_namespace
        else:
            # No planned entry depends on it — cannot infer target file.
            # This is unusual but not fatal. Use empty strings and let
            # the file manager handle it (or skip seeding).
            target_file = ""
            target_namespace = ""

        result.append(ExistingEntry(
            name=name,
            target_file=target_file,
            target_namespace=target_namespace,
            suggested_signature=raw.get("suggested_signature", ""),
            mathlib_reference=raw.get("mathlib_reference", ""),
            layer=raw.get("layer", ""),
        ))

    return result


def _find_first_dependent(
    name: str, planned: list[PlannedEntry]
) -> PlannedEntry | None:
    """Find the first planned entry (by order_index) that depends on `name`."""
    for entry in planned:  # already sorted by order_index
        if name in entry.depends_on:
            return entry
    return None


def _validate(
    entries: list[PlannedEntry],
    planned_names: set[str],
    spec_dir: Path,
) -> None:
    """Validate the execution plan.

    Checks:
      1. Every internal dependency references a known planned entry
         or is an external dep (not in planned_names → external, OK).
      2. Every planned entry has a corresponding spec file in lemma_specs/.
    """
    errors: list[str] = []

    for entry in entries:
        # Check spec file exists
        spec_path = spec_dir / entry.spec_file
        if not spec_path.exists():
            errors.append(
                f"Missing spec file for '{entry.name}': {spec_path}"
            )

    if errors:
        raise ValueError(
            "Blueprint validation failed:\n" + "\n".join(f"  - {e}" for e in errors)
        )
