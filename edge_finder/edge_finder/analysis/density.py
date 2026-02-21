"""Module 3a: Density & Structure Analyzer.

Computes aggregate structural metrics from search results: namespace declaration
counts, module spread ratio (how dispersed are results across modules), operator
hit ratio (what fraction of results look like operators), and namespace depths.

Namespace extraction uses the first two dot-segments (e.g., Finset.sum from
Finset.sum.comm), which provides meaningful sub-namespace granularity without
fragmenting into single-declaration buckets.

Operator detection uses suffix matching against common Mathlib operator patterns.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from edge_finder.search.models import SearchResponse, SearchResult


@dataclass(frozen=True)
class NamespaceStats:
    namespace: str
    declaration_count: int
    module_count: int


@dataclass(frozen=True)
class DensityReport:
    total_queries: int
    total_declarations: int
    namespaces: list[NamespaceStats]
    modules: list[str]
    operator_hits: list[str]
    unique_namespaces: int
    module_spread_ratio: float
    operator_hit_ratio: float
    namespace_depths: list[int]

    def to_dict(self) -> dict[str, object]:
        return {
            "total_queries": self.total_queries,
            "total_declarations": self.total_declarations,
            "unique_namespaces": self.unique_namespaces,
            "module_spread_ratio": self.module_spread_ratio,
            "operator_hit_ratio": self.operator_hit_ratio,
            "namespace_depths": self.namespace_depths,
            "namespaces": [
                {
                    "namespace": stats.namespace,
                    "declaration_count": stats.declaration_count,
                    "module_count": stats.module_count,
                }
                for stats in self.namespaces
            ],
            "modules": self.modules,
            "operator_hits": self.operator_hits,
        }


def _namespace_of(name: str) -> str:
    """Extract namespace from a declaration name using the first two dot-segments.

    Examples:
        "Finset.sum.comm"    -> "Finset.sum"
        "Finset.card"        -> "Finset.card"
        "Finset"             -> "Finset"
        "List.sum.eq_zero"   -> "List.sum"
    """
    parts = name.split(".")
    return ".".join(parts[:2]) if len(parts) >= 2 else name


def _namespace_depth(name: str) -> int:
    return len([part for part in name.split(".") if part])


_OPERATOR_SUFFIXES = (
    # Aggregation / folding
    ".sum",
    ".prod",
    ".fold",
    ".foldl",
    ".foldr",
    ".reduce",
    # Functorial / monadic
    ".map",
    ".bind",
    ".pure",
    ".filter",
    ".filterMap",
    # Algebraic operations
    ".add",
    ".mul",
    ".sub",
    ".div",
    ".neg",
    ".inv",
    ".pow",
    # Lattice / order
    ".sup",
    ".inf",
    ".max",
    ".min",
    # Set-like
    ".union",
    ".inter",
    ".sdiff",
    ".compl",
    # Composition / application
    ".comp",
    ".apply",
)


def _operator_candidates(results: Iterable[SearchResult]) -> list[str]:
    """Identify declarations that look like operator definitions.

    Uses suffix matching against common Mathlib operator patterns. This is
    deliberately conservative -- it identifies structural operators, not every
    function. The list covers aggregation, functorial, algebraic, lattice,
    set-theoretic, and composition patterns.
    """
    hits: list[str] = []
    for result in results:
        name_lower = result.name.lower()
        for suffix in _OPERATOR_SUFFIXES:
            if name_lower.endswith(suffix):
                hits.append(result.name)
                break
    return hits


def compute_density_report(responses: list[SearchResponse]) -> DensityReport:
    all_results: list[SearchResult] = []
    for response in responses:
        all_results.extend(response.results)

    namespace_counts: dict[str, int] = {}
    namespace_modules: dict[str, set[str]] = {}
    modules: set[str] = set()

    for result in all_results:
        namespace = _namespace_of(result.name)
        namespace_counts[namespace] = namespace_counts.get(namespace, 0) + 1
        namespace_modules.setdefault(namespace, set()).add(result.module)
        modules.add(result.module)

    namespace_stats = [
        NamespaceStats(
            namespace=namespace,
            declaration_count=count,
            module_count=len(namespace_modules[namespace]),
        )
        for namespace, count in namespace_counts.items()
    ]

    namespace_stats.sort(key=lambda item: item.declaration_count, reverse=True)

    operator_hits = _operator_candidates(all_results)
    namespace_depths = [_namespace_depth(result.name) for result in all_results]
    unique_namespaces = len(namespace_counts)
    module_spread_ratio = 0.0
    operator_hit_ratio = 0.0
    if all_results:
        module_spread_ratio = len(modules) / len(all_results)
        operator_hit_ratio = len(set(operator_hits)) / len(all_results)
    return DensityReport(
        total_queries=len(responses),
        total_declarations=len(all_results),
        namespaces=namespace_stats,
        modules=sorted(modules),
        operator_hits=sorted(set(operator_hits)),
        unique_namespaces=unique_namespaces,
        module_spread_ratio=round(module_spread_ratio, 4),
        operator_hit_ratio=round(operator_hit_ratio, 4),
        namespace_depths=namespace_depths,
    )
