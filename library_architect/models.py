"""
Data models for the Library Architect pipeline.

Defines the structured types that flow through the three-component pipeline:
  Decomposer → Grounder → Blueprint Assembler

All models are frozen dataclasses with JSON round-tripping support.
No model contains business logic — they are pure data carriers.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any


# ---------------------------------------------------------------------------
# Stage 1: Decomposer output
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DefinitionSketch:
    """A proposed Lean definition, as hypothesized by the Decomposer.

    This is a hypothesis, not a claim — grounding has not yet occurred.
    """
    name: str
    informal: str
    suggested_signature: str
    layer: str
    depends_on: list[str] = field(default_factory=list)
    mathlib_search_queries: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "informal": self.informal,
            "suggested_signature": self.suggested_signature,
            "layer": self.layer,
            "depends_on": self.depends_on,
            "mathlib_search_queries": self.mathlib_search_queries,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> DefinitionSketch:
        return cls(
            name=data["name"],
            informal=data["informal"],
            suggested_signature=data["suggested_signature"],
            layer=data.get("layer", ""),
            depends_on=data.get("depends_on", []),
            mathlib_search_queries=data.get("mathlib_search_queries", []),
        )


@dataclass(frozen=True)
class LemmaSketch:
    """A proposed lemma, as hypothesized by the Decomposer.

    This is a hypothesis, not a claim — grounding has not yet occurred.
    """
    name: str
    informal_statement: str
    suggested_signature: str
    depends_on: list[str]
    layer: str
    hints: str = ""
    difficulty: str = "medium"
    mathlib_search_queries: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "informal_statement": self.informal_statement,
            "suggested_signature": self.suggested_signature,
            "depends_on": self.depends_on,
            "layer": self.layer,
            "hints": self.hints,
            "difficulty": self.difficulty,
            "mathlib_search_queries": self.mathlib_search_queries,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> LemmaSketch:
        return cls(
            name=data["name"],
            informal_statement=data["informal_statement"],
            suggested_signature=data["suggested_signature"],
            depends_on=data.get("depends_on", []),
            layer=data.get("layer", ""),
            hints=data.get("hints", ""),
            difficulty=data.get("difficulty", "medium"),
            mathlib_search_queries=data.get("mathlib_search_queries", []),
        )


@dataclass(frozen=True)
class Decomposition:
    """Raw output of the Decomposer — ungrounded definitions and lemma sketches."""
    theme: str
    definitions: list[DefinitionSketch]
    lemmas: list[LemmaSketch]
    layers: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "theme": self.theme,
            "definitions": [d.to_dict() for d in self.definitions],
            "lemmas": [l.to_dict() for l in self.lemmas],
            "layers": self.layers,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> Decomposition:
        return cls(
            theme=data["theme"],
            definitions=[DefinitionSketch.from_dict(d) for d in data["definitions"]],
            lemmas=[LemmaSketch.from_dict(l) for l in data["lemmas"]],
            layers=data.get("layers", []),
        )


# ---------------------------------------------------------------------------
# Stage 2: Grounder output
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GroundingResult:
    """Classification of a single definition or lemma against Mathlib."""
    status: str  # "novel", "exists", "partial_overlap", "ungrounded"
    evidence: list[str] = field(default_factory=list)  # Mathlib declaration names found
    notes: str = ""
    source_snippets: list[dict[str, str]] = field(default_factory=list)
    """Top Mathlib source snippets from LeanExplore (name + source_text pairs).
    Used by the expansion prompt to ground Lean 4 signatures in real API usage."""

    def to_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "evidence": self.evidence,
            "notes": self.notes,
            "source_snippets": self.source_snippets,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> GroundingResult:
        return cls(
            status=data["status"],
            evidence=data.get("evidence", []),
            notes=data.get("notes", ""),
            source_snippets=data.get("source_snippets", []),
        )


@dataclass(frozen=True)
class GroundedDefinition:
    """A definition sketch with grounding classification."""
    sketch: DefinitionSketch
    grounding: GroundingResult

    def to_dict(self) -> dict[str, Any]:
        return {
            **self.sketch.to_dict(),
            "grounding": self.grounding.to_dict(),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> GroundedDefinition:
        grounding_data = data.get("grounding", {"status": "ungrounded"})
        return cls(
            sketch=DefinitionSketch.from_dict(data),
            grounding=GroundingResult.from_dict(grounding_data),
        )


@dataclass(frozen=True)
class GroundedLemma:
    """A lemma sketch with grounding classification."""
    sketch: LemmaSketch
    grounding: GroundingResult

    def to_dict(self) -> dict[str, Any]:
        return {
            **self.sketch.to_dict(),
            "grounding": self.grounding.to_dict(),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> GroundedLemma:
        grounding_data = data.get("grounding", {"status": "ungrounded"})
        return cls(
            sketch=LemmaSketch.from_dict(data),
            grounding=GroundingResult.from_dict(grounding_data),
        )


@dataclass(frozen=True)
class GroundedDecomposition:
    """Decomposition with grounding results for each definition and lemma."""
    theme: str
    definitions: list[GroundedDefinition]
    lemmas: list[GroundedLemma]
    layers: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "theme": self.theme,
            "definitions": [d.to_dict() for d in self.definitions],
            "lemmas": [l.to_dict() for l in self.lemmas],
            "layers": self.layers,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> GroundedDecomposition:
        return cls(
            theme=data["theme"],
            definitions=[GroundedDefinition.from_dict(d) for d in data["definitions"]],
            lemmas=[GroundedLemma.from_dict(l) for l in data["lemmas"]],
            layers=data.get("layers", []),
        )


# ---------------------------------------------------------------------------
# Stage 3: Blueprint Assembler output
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LemmaSpec:
    """Complete specification for the Proof Oracle.

    Matches the schema expected by proof_oracle.runner.orchestrator.run_lemma().
    """
    lemma_name: str
    target_file: str
    target_namespace: str
    informal_statement: str
    suggested_signature: str
    depends_on: list[str] = field(default_factory=list)
    hints: str = ""
    attempt_budget: int = 10
    difficulty: str = "medium"

    def to_dict(self) -> dict[str, Any]:
        return {
            "lemma_name": self.lemma_name,
            "target_file": self.target_file,
            "target_namespace": self.target_namespace,
            "informal_statement": self.informal_statement,
            "suggested_signature": self.suggested_signature,
            "depends_on": self.depends_on,
            "hints": self.hints,
            "attempt_budget": self.attempt_budget,
            "difficulty": self.difficulty,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> LemmaSpec:
        return cls(
            lemma_name=data["lemma_name"],
            target_file=data["target_file"],
            target_namespace=data.get("target_namespace", ""),
            informal_statement=data["informal_statement"],
            suggested_signature=data["suggested_signature"],
            depends_on=data.get("depends_on", []),
            hints=data.get("hints", ""),
            attempt_budget=data.get("attempt_budget", 10),
            difficulty=data.get("difficulty", "medium"),
        )


@dataclass(frozen=True)
class BlueprintEntry:
    """A single entry in the blueprint — either a definition or a lemma."""
    name: str
    entry_type: str  # "definition" or "lemma"
    status: str  # "planned", "exists_in_mathlib", "skipped"
    layer: str
    informal: str
    suggested_signature: str
    depends_on: list[str] = field(default_factory=list)
    grounding_status: str = "ungrounded"
    grounding_evidence: list[str] = field(default_factory=list)
    grounding_notes: str = ""
    mathlib_reference: str | None = None
    lemma_spec: LemmaSpec | None = None
    order_index: int = 0
    hints: str = ""
    difficulty: str = "medium"

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "name": self.name,
            "entry_type": self.entry_type,
            "status": self.status,
            "layer": self.layer,
            "informal": self.informal,
            "suggested_signature": self.suggested_signature,
            "depends_on": self.depends_on,
            "grounding_status": self.grounding_status,
            "grounding_evidence": self.grounding_evidence,
            "grounding_notes": self.grounding_notes,
            "mathlib_reference": self.mathlib_reference,
            "order_index": self.order_index,
            "hints": self.hints,
            "difficulty": self.difficulty,
        }
        if self.lemma_spec is not None:
            d["lemma_spec"] = self.lemma_spec.to_dict()
        return d

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> BlueprintEntry:
        spec_data = data.get("lemma_spec")
        spec = LemmaSpec.from_dict(spec_data) if spec_data else None
        return cls(
            name=data["name"],
            entry_type=data["entry_type"],
            status=data["status"],
            layer=data.get("layer", ""),
            informal=data.get("informal", ""),
            suggested_signature=data.get("suggested_signature", ""),
            depends_on=data.get("depends_on", []),
            grounding_status=data.get("grounding_status", "ungrounded"),
            grounding_evidence=data.get("grounding_evidence", []),
            grounding_notes=data.get("grounding_notes", ""),
            mathlib_reference=data.get("mathlib_reference"),
            lemma_spec=spec,
            order_index=data.get("order_index", 0),
            hints=data.get("hints", ""),
            difficulty=data.get("difficulty", "medium"),
        )


@dataclass(frozen=True)
class BlueprintSummary:
    """Aggregate statistics about the blueprint."""
    total_definitions: int
    total_lemmas: int
    planned_count: int
    exists_count: int
    skipped_count: int
    layers: list[str]

    def to_dict(self) -> dict[str, Any]:
        return {
            "total_definitions": self.total_definitions,
            "total_lemmas": self.total_lemmas,
            "planned_count": self.planned_count,
            "exists_count": self.exists_count,
            "skipped_count": self.skipped_count,
            "layers": self.layers,
        }


@dataclass(frozen=True)
class Blueprint:
    """The final output of the Library Architect pipeline.

    Contains a dependency-ordered plan of definitions and lemmas,
    each with a complete LemmaSpec for the Proof Oracle.
    """
    theme: str
    entries: list[BlueprintEntry]
    dependency_dag: dict[str, list[str]]
    summary: BlueprintSummary

    def to_dict(self) -> dict[str, Any]:
        return {
            "theme": self.theme,
            "entries": [e.to_dict() for e in self.entries],
            "dependency_dag": self.dependency_dag,
            "summary": self.summary.to_dict(),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> Blueprint:
        summary_data = data["summary"]
        return cls(
            theme=data["theme"],
            entries=[BlueprintEntry.from_dict(e) for e in data["entries"]],
            dependency_dag=data["dependency_dag"],
            summary=BlueprintSummary(**summary_data),
        )

    def to_json(self, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent)

    @classmethod
    def from_json(cls, text: str) -> Blueprint:
        return cls.from_dict(json.loads(text))
