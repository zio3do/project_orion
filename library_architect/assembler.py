"""
Blueprint Assembler — Stage 3 of the Library Architect pipeline.

Takes a GroundedDecomposition and produces a Blueprint: a dependency-ordered
plan with complete LemmaSpec entries, serialized as BLUEPRINT.md + blueprint.json.

This component is purely algorithmic — no LLM calls. It:
  1. Builds the dependency DAG from depends_on fields.
  2. Validates acyclicity via topological sort.
  3. Marks existing Mathlib entries and adjusts dependencies.
  4. Assembles complete LemmaSpec entries for novel/partial items.
  5. Generates the dual-format output.
"""

from __future__ import annotations

import json
from collections import defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from library_architect.models import (
    Blueprint,
    BlueprintEntry,
    BlueprintSummary,
    GroundedDecomposition,
    GroundedDefinition,
    GroundedLemma,
    LemmaSpec,
)


def _theme_to_pascal(theme: str) -> str:
    """Convert a theme name to PascalCase for directory/namespace use.

    Handles both space-separated ('Graded Order Combinatorics' →
    'GradedOrderCombinatorics') and already-PascalCase inputs.
    """
    if " " in theme:
        return "".join(word.capitalize() for word in theme.split())
    return theme[0].upper() + theme[1:] if theme else theme


def _layer_to_pascal(layer: str) -> str:
    """Convert a layer name to PascalCase for file naming.

    Handles both space-separated ('Level Sets' → 'LevelSets') and
    already-PascalCase ('LevelSets' → 'LevelSets') inputs.
    """
    if " " in layer:
        return "".join(word.capitalize() for word in layer.split())
    # Already a single token — assume PascalCase, just ensure first char is upper.
    return layer[0].upper() + layer[1:] if layer else layer


def _target_file(theme: str, layer: str) -> str:
    """Derive the target Lean file path from theme and layer."""
    theme_dir = _theme_to_pascal(theme)
    layer_file = _layer_to_pascal(layer)
    return f"Orion/{theme_dir}/{layer_file}.lean"


def _target_namespace(theme: str, layer: str) -> str:
    """Derive the target Lean namespace from theme and layer."""
    theme_ns = _theme_to_pascal(theme)
    layer_ns = _layer_to_pascal(layer)
    return f"Orion.{theme_ns}.{layer_ns}"


def _topological_sort(dag: dict[str, list[str]], all_names: set[str]) -> list[str]:
    """Topological sort of a DAG. Raises ValueError if cycles detected.

    Args:
        dag: adjacency list (name → list of dependencies).
        all_names: set of all node names.

    Returns:
        List of names in topological order (dependencies first).
    """
    # Compute in-degree for each node.
    in_degree: dict[str, int] = {name: 0 for name in all_names}
    # Build reverse adjacency: for each dependency, the node depends on it.
    for name, deps in dag.items():
        for dep in deps:
            if dep in in_degree:
                in_degree[name] = in_degree.get(name, 0)  # ensure exists
                # dep must come before name — so name has an incoming edge from dep.

    # Recompute properly: in_degree[x] = number of nodes that x depends on
    # (i.e., number of edges pointing into x in a "must come after" sense).
    # Actually, for topological sort, in_degree[x] = number of prerequisites of x.
    in_degree = {name: 0 for name in all_names}
    for name, deps in dag.items():
        for dep in deps:
            if dep in all_names:
                in_degree[name] += 1

    # Kahn's algorithm.
    queue: deque[str] = deque()
    for name in all_names:
        if in_degree[name] == 0:
            queue.append(name)

    # Build reverse map: dep → list of dependents.
    dependents: dict[str, list[str]] = defaultdict(list)
    for name, deps in dag.items():
        for dep in deps:
            if dep in all_names:
                dependents[dep].append(name)

    result: list[str] = []
    while queue:
        node = queue.popleft()
        result.append(node)
        for dependent in dependents[node]:
            in_degree[dependent] -= 1
            if in_degree[dependent] == 0:
                queue.append(dependent)

    if len(result) != len(all_names):
        sorted_set = set(result)
        cycle_members = all_names - sorted_set
        raise ValueError(
            f"Dependency cycle detected among: {cycle_members}. "
            f"Cannot produce a valid build order."
        )

    return result


def _build_entry(
    name: str,
    entry_type: str,
    informal: str,
    suggested_signature: str,
    layer: str,
    depends_on: list[str],
    grounding_status: str,
    grounding_evidence: list[str],
    grounding_notes: str,
    hints: str,
    difficulty: str,
    theme: str,
    order_index: int,
) -> BlueprintEntry:
    """Build a single BlueprintEntry with its LemmaSpec (if planned)."""
    # Determine status based on grounding.
    if grounding_status == "exists":
        status = "exists_in_mathlib"
        mathlib_ref = grounding_evidence[0] if grounding_evidence else None
        spec = None
    else:
        status = "planned"
        mathlib_ref = None

        # Filter depends_on to only include names that are part of our blueprint
        # (not Mathlib references). The Proof Oracle will find Mathlib deps via search.
        target_f = _target_file(theme, layer)
        target_ns = _target_namespace(theme, layer)

        spec = LemmaSpec(
            lemma_name=name,
            target_file=target_f,
            target_namespace=target_ns,
            informal_statement=informal,
            suggested_signature=suggested_signature,
            depends_on=depends_on,
            hints=hints,
            attempt_budget=10,
            difficulty=difficulty,
        )

    return BlueprintEntry(
        name=name,
        entry_type=entry_type,
        status=status,
        layer=layer,
        informal=informal,
        suggested_signature=suggested_signature,
        depends_on=depends_on,
        grounding_status=grounding_status,
        grounding_evidence=grounding_evidence,
        grounding_notes=grounding_notes,
        mathlib_reference=mathlib_ref,
        lemma_spec=spec,
        order_index=order_index,
        hints=hints,
        difficulty=difficulty,
    )


def _generate_blueprint_md(blueprint: Blueprint, theme_doc_path: str | None) -> str:
    """Generate the human-readable BLUEPRINT.md content."""
    lines: list[str] = []
    now = datetime.now(timezone.utc).isoformat()

    lines.append(f"# Blueprint: {blueprint.theme}")
    lines.append("")
    lines.append(f"Generated: {now}")
    if theme_doc_path:
        lines.append(f"Theme document: {theme_doc_path}")
    lines.append("")

    # Summary section.
    s = blueprint.summary
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Definitions: {s.total_definitions}")
    lines.append(f"- Lemmas: {s.total_lemmas}")
    lines.append(f"- Planned: {s.planned_count}")
    lines.append(f"- Exists in Mathlib: {s.exists_count}")
    lines.append(f"- Skipped: {s.skipped_count}")
    lines.append(f"- Layers: {len(s.layers)} ({', '.join(s.layers)})")
    lines.append("")

    # Dependency graph section.
    lines.append("## Dependency Graph")
    lines.append("")
    for name, deps in sorted(blueprint.dependency_dag.items()):
        if deps:
            lines.append(f"{name} depends on: {', '.join(deps)}")
        else:
            lines.append(f"{name} (no dependencies)")
    lines.append("")

    # Entries by layer.
    entries_by_layer: dict[str, list[BlueprintEntry]] = defaultdict(list)
    for entry in blueprint.entries:
        entries_by_layer[entry.layer].append(entry)

    for layer in blueprint.summary.layers:
        layer_entries = entries_by_layer.get(layer, [])
        if not layer_entries:
            continue

        lines.append(f"## {layer}")
        lines.append("")

        for entry in layer_entries:
            kind = "DEF" if entry.entry_type == "definition" else "LEMMA"
            lines.append(f"### {kind} {entry.name}")
            lines.append("")
            lines.append(f"- status: {entry.status}")
            lines.append(f"- signature: `{entry.suggested_signature}`")
            lines.append(f"- informal: {entry.informal}")
            lines.append(f"- grounding: {entry.grounding_status}"
                        f"{' (' + entry.grounding_notes + ')' if entry.grounding_notes else ''}")
            if entry.depends_on:
                lines.append(f"- depends_on: {', '.join(entry.depends_on)}")
            if entry.hints:
                lines.append(f"- hints: {entry.hints}")
            if entry.entry_type == "lemma":
                lines.append(f"- difficulty: {entry.difficulty}")
            if entry.mathlib_reference:
                lines.append(f"- mathlib_reference: {entry.mathlib_reference}")
            lines.append("")

    # Handle entries with no layer.
    no_layer = entries_by_layer.get("", [])
    if no_layer:
        lines.append("## Uncategorized")
        lines.append("")
        for entry in no_layer:
            kind = "DEF" if entry.entry_type == "definition" else "LEMMA"
            lines.append(f"### {kind} {entry.name}")
            lines.append("")
            lines.append(f"- status: {entry.status}")
            lines.append(f"- signature: `{entry.suggested_signature}`")
            lines.append(f"- informal: {entry.informal}")
            lines.append(f"- grounding: {entry.grounding_status}")
            lines.append("")

    return "\n".join(lines)


def assemble(
    grounded: GroundedDecomposition,
    *,
    output_dir: Path | None = None,
    theme_doc_path: str | None = None,
) -> Blueprint:
    """Assemble a Blueprint from a GroundedDecomposition.

    Builds the dependency DAG, validates acyclicity, assembles LemmaSpecs,
    and writes BLUEPRINT.md + blueprint.json.

    Args:
        grounded: The grounded decomposition from the Grounder.
        output_dir: Where to write output files. If None, files are not written.
        theme_doc_path: Path to the theme doc (for BLUEPRINT.md header).

    Returns:
        The assembled Blueprint.

    Raises:
        ValueError: If the dependency graph contains cycles.
    """
    theme = grounded.theme

    # Collect all names and build the DAG.
    all_names: set[str] = set()
    dag: dict[str, list[str]] = {}

    for defn in grounded.definitions:
        all_names.add(defn.sketch.name)
        dag[defn.sketch.name] = defn.sketch.depends_on

    for lemma in grounded.lemmas:
        all_names.add(lemma.sketch.name)
        dag[lemma.sketch.name] = lemma.sketch.depends_on

    # Add any dependency names that aren't in our blueprint as phantom nodes
    # (they might reference Mathlib or other external entries).
    all_dep_names: set[str] = set()
    for deps in dag.values():
        all_dep_names.update(deps)
    external_deps = all_dep_names - all_names
    # Don't add external deps to the sort — they're assumed to exist.
    # Filter them out of the dag for topological sort purposes.
    dag_internal: dict[str, list[str]] = {}
    for name in all_names:
        dag_internal[name] = [d for d in dag.get(name, []) if d in all_names]

    # Topological sort.
    sorted_names = _topological_sort(dag_internal, all_names)

    # Build a lookup for grounded items.
    def_lookup: dict[str, GroundedDefinition] = {
        d.sketch.name: d for d in grounded.definitions
    }
    lemma_lookup: dict[str, GroundedLemma] = {
        l.sketch.name: l for l in grounded.lemmas
    }

    # Assemble entries in topological order.
    entries: list[BlueprintEntry] = []
    for idx, name in enumerate(sorted_names):
        if name in def_lookup:
            gd = def_lookup[name]
            entry = _build_entry(
                name=gd.sketch.name,
                entry_type="definition",
                informal=gd.sketch.informal,
                suggested_signature=gd.sketch.suggested_signature,
                layer=gd.sketch.layer,
                depends_on=dag.get(name, []),
                grounding_status=gd.grounding.status,
                grounding_evidence=gd.grounding.evidence,
                grounding_notes=gd.grounding.notes,
                hints="",
                difficulty="easy",
                theme=theme,
                order_index=idx,
            )
            entries.append(entry)
        elif name in lemma_lookup:
            gl = lemma_lookup[name]
            entry = _build_entry(
                name=gl.sketch.name,
                entry_type="lemma",
                informal=gl.sketch.informal_statement,
                suggested_signature=gl.sketch.suggested_signature,
                layer=gl.sketch.layer,
                depends_on=gl.sketch.depends_on,
                grounding_status=gl.grounding.status,
                grounding_evidence=gl.grounding.evidence,
                grounding_notes=gl.grounding.notes,
                hints=gl.sketch.hints,
                difficulty=gl.sketch.difficulty,
                theme=theme,
                order_index=idx,
            )
            entries.append(entry)

    # Build summary.
    total_defs = sum(1 for e in entries if e.entry_type == "definition")
    total_lemmas = sum(1 for e in entries if e.entry_type == "lemma")
    planned = sum(1 for e in entries if e.status == "planned")
    exists_count = sum(1 for e in entries if e.status == "exists_in_mathlib")
    skipped = sum(1 for e in entries if e.status == "skipped")

    summary = BlueprintSummary(
        total_definitions=total_defs,
        total_lemmas=total_lemmas,
        planned_count=planned,
        exists_count=exists_count,
        skipped_count=skipped,
        layers=grounded.layers,
    )

    blueprint = Blueprint(
        theme=theme,
        entries=entries,
        dependency_dag=dag,
        summary=summary,
    )

    # Write output files if directory specified.
    if output_dir is not None:
        output_dir.mkdir(parents=True, exist_ok=True)

        # BLUEPRINT.md
        md_content = _generate_blueprint_md(blueprint, theme_doc_path)
        (output_dir / "BLUEPRINT.md").write_text(md_content, encoding="utf-8")

        # blueprint.json
        json_content = blueprint.to_json(indent=2)
        (output_dir / "blueprint.json").write_text(json_content, encoding="utf-8")

        # Also write individual lemma specs for easy Proof Oracle consumption.
        specs_dir = output_dir / "lemma_specs"
        specs_dir.mkdir(exist_ok=True)
        for entry in entries:
            if entry.lemma_spec is not None:
                spec_path = specs_dir / f"{entry.name}.json"
                spec_path.write_text(
                    json.dumps(entry.lemma_spec.to_dict(), indent=2),
                    encoding="utf-8",
                )

    return blueprint
