"""
Grounder — Stage 2 of the Library Architect pipeline.

Takes a raw Decomposition and checks each definition/lemma against Mathlib
via the LeanExplore HTTP API. Classifies each as novel, exists, or
partial_overlap.

No LLM calls — purely search API + heuristic classification.
Every search query is logged for auditability.

Uses direct HTTP calls to the LeanExplore API rather than importing the
lean_explore library, to avoid the Python 3.10+ dependency chain.

Resilience patterns (adopted from Edge Finder):
  - Retry on 5xx AND 429 with exponential backoff
  - Explicit httpx timeout (30s)
  - Inter-request spacing (100ms) to avoid tripping rate limits
  - Client-side result slicing (API may ignore limit parameter)
  - Per-query error isolation (failed query → empty response, not crash)
  - Shared httpx client across all queries in a batch
"""

from __future__ import annotations

import asyncio
import json
import hashlib
import logging
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import httpx

from library_architect.models import (
    Decomposition,
    DefinitionSketch,
    GroundedDecomposition,
    GroundedDefinition,
    GroundedLemma,
    GroundingResult,
    LemmaSketch,
)

logger = logging.getLogger(__name__)

# LeanExplore API endpoint (v2, canonical).
LEANEXPLORE_API_URL = "https://www.leanexplore.com/api/v2/search"

# Retry configuration for transient server errors and rate limiting.
MAX_RETRIES = 3
RETRY_BASE_DELAY_S = 1.0  # Exponential backoff: 1s, 2s, 4s

# Inter-request spacing to avoid rate-limit triggering.
INTER_REQUEST_DELAY_S = 0.1

# Explicit request timeout (seconds).
REQUEST_TIMEOUT_S = 30.0

# Maximum results to accept per query (client-side slicing).
MAX_RESULTS_PER_QUERY = 20

# Cache directory for grounding results.
CACHE_DIR = Path("library_architect/.cache/grounding")


@dataclass(frozen=True)
class SearchResult:
    """A single search result from LeanExplore."""
    name: str
    module: str = ""
    docstring: str = ""
    informalization: str = ""
    source_text: str = ""

    @classmethod
    def from_api(cls, data: dict[str, Any]) -> SearchResult:
        return cls(
            name=data.get("name", data.get("declaration_name", "")),
            module=data.get("module", data.get("module_name", "")),
            docstring=data.get("docstring", "") or "",
            informalization=data.get("informalization", "") or "",
            source_text=data.get("source_text", "") or "",
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "module": self.module,
            "docstring": self.docstring,
            "informalization": self.informalization,
            "source_text": self.source_text,
        }


@dataclass(frozen=True)
class SearchResponse:
    """Response from a single LeanExplore search query."""
    query: str
    results: list[SearchResult] = field(default_factory=list)
    count: int = 0
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "query": self.query,
            "results": [r.to_dict() for r in self.results],
            "count": self.count,
            "elapsed_ms": self.elapsed_ms,
        }


# ---------------------------------------------------------------------------
# Cache
# ---------------------------------------------------------------------------

def _cache_key(query: str, limit: int) -> str:
    """Deterministic cache key for a query."""
    raw = f"{query}|{limit}"
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def _load_cached(query: str, limit: int) -> SearchResponse | None:
    """Load a cached search response, or None if not cached."""
    if not CACHE_DIR.exists():
        return None
    path = CACHE_DIR / f"{_cache_key(query, limit)}.json"
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        results = [SearchResult(**r) for r in data.get("results", [])]
        return SearchResponse(
            query=data["query"],
            results=results,
            count=data.get("count", len(results)),
            elapsed_ms=data.get("elapsed_ms", 0.0),
        )
    except Exception as exc:
        logger.debug("Cache read failed for %r: %s", query, exc)
        return None


def _save_to_cache(response: SearchResponse, limit: int) -> None:
    """Persist a search response to disk cache."""
    try:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        path = CACHE_DIR / f"{_cache_key(response.query, limit)}.json"
        path.write_text(
            json.dumps(response.to_dict(), indent=2),
            encoding="utf-8",
        )
    except Exception as exc:
        logger.debug("Cache write failed for %r: %s", response.query, exc)


# ---------------------------------------------------------------------------
# API calls
# ---------------------------------------------------------------------------

async def _search_leanexplore(
    query: str,
    *,
    client: httpx.AsyncClient,
    api_key: str = "",
    limit: int = 10,
    use_cache: bool = True,
) -> SearchResponse:
    """Search LeanExplore via direct HTTP call with retry on 5xx and 429.

    Returns an empty SearchResponse on failure rather than crashing.
    Patterns adopted from the Edge Finder's search module.
    """
    # Check cache first.
    if use_cache:
        cached = _load_cached(query, limit)
        if cached is not None:
            logger.debug("Cache hit for %r", query)
            return cached

    headers: dict[str, str] = {}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    params = {"q": query, "limit": limit}

    last_exc: Exception | None = None
    t0 = time.monotonic()

    for attempt in range(1 + MAX_RETRIES):
        try:
            resp = await client.get(
                LEANEXPLORE_API_URL,
                params=params,
                headers=headers,
            )
            resp.raise_for_status()
            data = resp.json()

            # Parse results — handle both array and object responses.
            if isinstance(data, list):
                raw_results = data
            elif isinstance(data, dict):
                raw_results = data.get("results", data.get("data", []))
            else:
                raw_results = []

            # Client-side slicing — API may ignore limit parameter.
            results = [
                SearchResult.from_api(item)
                for item in raw_results[:MAX_RESULTS_PER_QUERY]
            ]

            elapsed = (time.monotonic() - t0) * 1000
            response = SearchResponse(
                query=query,
                results=results,
                count=len(results),
                elapsed_ms=elapsed,
            )

            # Cache successful responses.
            if use_cache:
                _save_to_cache(response, limit)

            return response

        except httpx.HTTPStatusError as exc:
            status = exc.response.status_code
            is_retryable = status >= 500 or status == 429
            if is_retryable and attempt < MAX_RETRIES:
                delay = RETRY_BASE_DELAY_S * (2 ** attempt)
                kind = "429 rate-limit" if status == 429 else f"{status} server error"
                logger.info(
                    "LeanExplore %s for %r (attempt %d/%d), retrying in %.1fs",
                    kind, query, attempt + 1, 1 + MAX_RETRIES, delay,
                )
                last_exc = exc
                await asyncio.sleep(delay)
                continue
            logger.warning("LeanExplore search failed for %r: %s", query, exc)
            return SearchResponse(query=query)

        except (httpx.TimeoutException, httpx.ConnectError) as exc:
            if attempt < MAX_RETRIES:
                delay = RETRY_BASE_DELAY_S * (2 ** attempt)
                logger.info(
                    "LeanExplore timeout/connect error for %r (attempt %d/%d), retrying in %.1fs",
                    query, attempt + 1, 1 + MAX_RETRIES, delay,
                )
                last_exc = exc
                await asyncio.sleep(delay)
                continue
            logger.warning("LeanExplore search failed for %r: %s", query, exc)
            return SearchResponse(query=query)

        except Exception as exc:
            logger.warning("LeanExplore search failed for %r: %s", query, exc)
            return SearchResponse(query=query)

    return SearchResponse(query=query)


def _classify(
    name: str,
    search_responses: list[SearchResponse],
) -> GroundingResult:
    """Classify a definition/lemma based on LeanExplore search results.

    Classification rules:
      - "exists"          : a result name closely matches the proposal name
      - "partial_overlap" : related results found but no exact match
      - "novel"           : no relevant results found
      - "ungrounded"      : search failed (empty responses due to API error)

    This is a conservative heuristic — it prefers "partial_overlap" over
    false "exists" classifications. Human review catches misclassifications.

    Also collects source_text snippets from top results for use in the
    expansion prompt (grounding the LLM in real Mathlib API usage).
    """
    all_results: list[SearchResult] = []
    for resp in search_responses:
        all_results.extend(resp.results)

    if not all_results:
        any_queries_ran = any(resp.query for resp in search_responses)
        if any_queries_ran:
            return GroundingResult(
                status="novel",
                evidence=[],
                notes=f"Searched {len(search_responses)} queries, found 0 results.",
            )
        return GroundingResult(
            status="ungrounded",
            evidence=[],
            notes="No search queries were available or all searches failed.",
        )

    # Deduplicate by name across all query responses.
    result_names = [r.name for r in all_results if r.name]
    unique_names = list(dict.fromkeys(result_names))

    # Collect source snippets from top results (deduplicated by name).
    seen_snippet_names: set[str] = set()
    source_snippets: list[dict[str, str]] = []
    for r in all_results:
        if r.name and r.source_text and r.name not in seen_snippet_names:
            seen_snippet_names.add(r.name)
            source_snippets.append({"name": r.name, "source_text": r.source_text})
            if len(source_snippets) >= 5:
                break

    # Check for exact or close name match.
    name_lower = name.lower().replace("_", "").replace(".", "")
    for rname in unique_names:
        rname_lower = rname.lower().replace("_", "").replace(".", "")
        if name_lower in rname_lower or rname_lower.endswith(name_lower):
            # Place the matched name first in evidence.
            other_names = [n for n in unique_names if n != rname][:4]
            return GroundingResult(
                status="exists",
                evidence=[rname] + other_names,
                notes=f"Close match found: {rname}",
                source_snippets=source_snippets,
            )

    # Partial overlap — any results with meaningful content.
    if len(unique_names) >= 2:
        return GroundingResult(
            status="partial_overlap",
            evidence=unique_names[:5],
            notes=f"Found {len(unique_names)} related declarations, no exact match.",
            source_snippets=source_snippets,
        )

    if len(unique_names) == 1:
        return GroundingResult(
            status="partial_overlap",
            evidence=unique_names,
            notes=f"Found 1 related declaration: {unique_names[0]}",
            source_snippets=source_snippets,
        )

    return GroundingResult(
        status="novel",
        evidence=[],
        notes=f"Searched {len(search_responses)} queries, no relevant results.",
    )


async def _ground_single(
    name: str,
    queries: list[str],
    *,
    client: httpx.AsyncClient,
    api_key: str,
    limit: int,
    use_cache: bool = True,
) -> GroundingResult:
    """Search LeanExplore for a single definition/lemma and classify.

    Runs queries sequentially with inter-request spacing.
    """
    responses: list[SearchResponse] = []
    for i, query in enumerate(queries):
        if i > 0:
            await asyncio.sleep(INTER_REQUEST_DELAY_S)
        resp = await _search_leanexplore(
            query,
            client=client,
            api_key=api_key,
            limit=limit,
            use_cache=use_cache,
        )
        responses.append(resp)

    return _classify(name, responses)


async def _ground_all(
    decomposition: Decomposition,
    api_key: str,
    limit: int,
    *,
    use_cache: bool = True,
) -> GroundedDecomposition:
    """Ground all definitions and lemmas against LeanExplore.

    Uses a shared httpx client for connection reuse across all queries.
    """
    grounded_defs: list[GroundedDefinition] = []
    grounded_lemmas: list[GroundedLemma] = []

    total = len(decomposition.definitions) + len(decomposition.lemmas)
    done = 0

    async with httpx.AsyncClient(timeout=REQUEST_TIMEOUT_S) as client:
        for defn in decomposition.definitions:
            result = await _ground_single(
                defn.name,
                defn.mathlib_search_queries,
                client=client,
                api_key=api_key,
                limit=limit,
                use_cache=use_cache,
            )
            done += 1
            print(f"  [grounder] ({done}/{total}) {defn.name}: {result.status}")
            grounded_defs.append(GroundedDefinition(sketch=defn, grounding=result))

            # Inter-item spacing.
            if done < total:
                await asyncio.sleep(INTER_REQUEST_DELAY_S)

        for lemma in decomposition.lemmas:
            result = await _ground_single(
                lemma.name,
                lemma.mathlib_search_queries,
                client=client,
                api_key=api_key,
                limit=limit,
                use_cache=use_cache,
            )
            done += 1
            print(f"  [grounder] ({done}/{total}) {lemma.name}: {result.status}")
            grounded_lemmas.append(GroundedLemma(sketch=lemma, grounding=result))

            # Inter-item spacing.
            if done < total:
                await asyncio.sleep(INTER_REQUEST_DELAY_S)

    return GroundedDecomposition(
        theme=decomposition.theme,
        definitions=grounded_defs,
        lemmas=grounded_lemmas,
        layers=decomposition.layers,
    )


def ground(
    decomposition: Decomposition,
    *,
    results_per_query: int = 10,
    use_cache: bool = True,
) -> GroundedDecomposition:
    """Ground a decomposition against Mathlib via LeanExplore.

    Runs search queries for each proposed definition and lemma, then
    classifies each as novel, exists, partial_overlap, or ungrounded.

    Args:
        decomposition: Raw decomposition from the Decomposer.
        results_per_query: Max results per LeanExplore query.
        use_cache: Whether to use disk cache for search results.

    Returns:
        A GroundedDecomposition with classification for each entry.
    """
    api_key = os.environ.get("LEANEXPLORE_API_KEY", "")
    return asyncio.run(
        _ground_all(decomposition, api_key, results_per_query, use_cache=use_cache)
    )


def _skeleton_search_queries(name: str, informal: str) -> list[str]:
    """Generate search queries from a skeleton item's name and description.

    Skeleton items don't have mathlib_search_queries yet (those come from
    the expansion pass). We synthesize reasonable queries from the name and
    informal description so the skeleton grounding pass can collect Mathlib
    source snippets.

    Strategy:
      1. The item name itself (often matches or is close to a Mathlib name).
      2. Key terms from the informal description (first ~60 chars, stripped
         of common filler words).
    """
    queries = [name]

    # Extract a second query from the informal description if available.
    if informal:
        # Use the first sentence or up to 60 characters, whichever is shorter.
        desc = informal.strip()
        dot_idx = desc.find(".")
        if 0 < dot_idx < 80:
            desc = desc[:dot_idx]
        elif len(desc) > 60:
            desc = desc[:60]
        # Only add if meaningfully different from the name.
        if desc.lower().replace("_", " ") != name.lower().replace("_", " "):
            queries.append(desc)

    return queries


def ground_skeleton(
    skeleton: dict[str, Any],
    theme: str,
    *,
    results_per_query: int = 10,
    use_cache: bool = True,
) -> GroundedDecomposition:
    """Ground a raw skeleton dict against Mathlib to collect source snippets.

    This is the lightweight grounding pass that runs between the skeleton and
    expansion stages in the grounded pipeline. Its primary purpose is to
    collect Mathlib source_text snippets that will be injected into the
    expansion prompt, grounding the LLM's signatures in real API usage.

    Since skeleton items don't yet have mathlib_search_queries (those come
    from the expansion pass), we synthesize queries from each item's name
    and informal description.

    Args:
        skeleton: Raw skeleton dict from skeleton_pass() with definitions,
            lemmas, and layers.
        theme: The theme name.
        results_per_query: Max results per LeanExplore query.
        use_cache: Whether to use disk cache for search results.

    Returns:
        A GroundedDecomposition with source_snippets populated for each item.
    """
    # Convert skeleton dict → Decomposition with synthesized search queries.
    definitions = []
    for d in skeleton.get("definitions", []):
        name = d["name"]
        informal = d.get("informal", "")
        definitions.append(DefinitionSketch(
            name=name,
            informal=informal,
            suggested_signature="",  # Not yet available.
            layer=d.get("layer", ""),
            depends_on=d.get("depends_on", []),
            mathlib_search_queries=_skeleton_search_queries(name, informal),
        ))

    lemmas = []
    for l in skeleton.get("lemmas", []):
        name = l["name"]
        informal = l.get("informal_statement", l.get("informal", ""))
        lemmas.append(LemmaSketch(
            name=name,
            informal_statement=informal,
            suggested_signature="",  # Not yet available.
            depends_on=l.get("depends_on", []),
            layer=l.get("layer", ""),
            mathlib_search_queries=_skeleton_search_queries(name, informal),
        ))

    decomposition = Decomposition(
        theme=theme,
        definitions=definitions,
        lemmas=lemmas,
        layers=skeleton.get("layers", []),
    )

    return ground(
        decomposition,
        results_per_query=results_per_query,
        use_cache=use_cache,
    )
