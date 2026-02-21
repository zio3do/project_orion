"""Data models for search results.

Defines SearchResult and SearchResponse as frozen dataclasses. SearchResult
represents a single Mathlib declaration returned by a search query, with fields
for name, module, docstring, source text, dependencies, and informalization.
SearchResponse wraps a list of SearchResult objects with the originating query
and metadata. Both classes support JSON round-tripping via to_dict()/from_dict()
and adaptation from the lean_explore library via from_lean_explore().
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from typing import Any, Optional


@dataclass(frozen=True)
class SearchResult:
    declaration_id: int
    name: str
    module: str
    docstring: Optional[str]
    source_text: str
    source_link: str
    dependencies: Optional[list[str]]
    informalization: Optional[str]

    @staticmethod
    def _parse_dependencies(raw: Any) -> Optional[list[str]]:
        if raw is None:
            return None
        if isinstance(raw, list):
            return [str(item) for item in raw]
        if isinstance(raw, str):
            try:
                parsed = json.loads(raw)
            except json.JSONDecodeError:
                return [raw]
            if isinstance(parsed, list):
                return [str(item) for item in parsed]
            return [str(parsed)]
        return [str(raw)]

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "SearchResult":
        return cls(
            declaration_id=int(data["id"]),
            name=str(data["name"]),
            module=str(data["module"]),
            docstring=data.get("docstring"),
            source_text=str(data.get("source_text", "")),
            source_link=str(data.get("source_link", "")),
            dependencies=cls._parse_dependencies(data.get("dependencies")),
            informalization=data.get("informalization"),
        )

    @classmethod
    def from_lean_explore(cls, result: Any) -> "SearchResult":
        return cls(
            declaration_id=int(result.id),
            name=str(result.name),
            module=str(result.module),
            docstring=getattr(result, "docstring", None),
            source_text=str(getattr(result, "source_text", "")),
            source_link=str(getattr(result, "source_link", "")),
            dependencies=cls._parse_dependencies(getattr(result, "dependencies", None)),
            informalization=getattr(result, "informalization", None),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.declaration_id,
            "name": self.name,
            "module": self.module,
            "docstring": self.docstring,
            "source_text": self.source_text,
            "source_link": self.source_link,
            "dependencies": self.dependencies,
            "informalization": self.informalization,
        }


@dataclass(frozen=True)
class SearchResponse:
    query: str
    results: list[SearchResult]
    count: int
    processing_time_ms: Optional[int]

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "SearchResponse":
        raw_results = data.get("results", [])
        results = [SearchResult.from_dict(item) for item in raw_results]
        count = int(data.get("count", len(results)))
        processing_time_ms = data.get("processing_time_ms")
        if processing_time_ms is not None:
            processing_time_ms = int(processing_time_ms)
        return cls(
            query=str(data.get("query", "")),
            results=results,
            count=count,
            processing_time_ms=processing_time_ms,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "query": self.query,
            "results": [result.to_dict() for result in self.results],
            "count": self.count,
            "processing_time_ms": self.processing_time_ms,
        }
