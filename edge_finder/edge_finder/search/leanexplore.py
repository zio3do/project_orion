"""Async wrapper around the LeanExplore API for Mathlib semantic search.

Provides a thin adapter that takes a list of natural-language queries, runs each
against the LeanExplore API sequentially, and converts the upstream response
objects into the edge finder's internal SearchResponse/SearchResult dataclasses.

Provides two public async functions:
  - search_queries(): batch search for a list of queries (used for theme-level search)
  - search_single(): search a single query (used for per-concept targeted search)

Both functions include retry logic with exponential backoff for transient server
errors (HTTP 5xx). This addresses the LeanExplore 500-error problem observed in
Iteration 5 calibration runs where 131/131 targeted queries failed due to
transient server issues.

Currently the only search mechanism in the pipeline (no Lean LSP, no grep fallback).
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
from typing import Iterable

import logging

import httpx
from lean_explore.api.client import ApiClient
from lean_explore.models import SearchResponse as LeanExploreResponse

from edge_finder.search.models import SearchResponse, SearchResult

logger = logging.getLogger(__name__)

# Retry configuration for transient server errors (5xx).
MAX_RETRIES = 2
RETRY_BASE_DELAY_S = 1.0  # Exponential backoff: 1s, 2s


@dataclass(frozen=True)
class LeanExploreConfig:
    api_key: str | None = None
    limit: int = 20
    packages: list[str] | None = None


async def _search_with_retry(
    client: ApiClient,
    query: str,
    limit: int,
    packages: list[str] | None,
) -> LeanExploreResponse:
    """Execute a single search with retry on transient (5xx) errors.

    Retries up to MAX_RETRIES times with exponential backoff. Only retries
    on HTTP 5xx status errors; other exceptions propagate immediately.
    """
    last_exc: Exception | None = None
    for attempt in range(1 + MAX_RETRIES):
        try:
            return await client.search(
                query=query,
                limit=limit,
                packages=packages,
            )
        except httpx.HTTPStatusError as exc:
            if exc.response.status_code >= 500 and attempt < MAX_RETRIES:
                delay = RETRY_BASE_DELAY_S * (2**attempt)
                logger.info(
                    "LeanExplore 5xx for %r (attempt %d/%d), retrying in %.1fs",
                    query,
                    attempt + 1,
                    1 + MAX_RETRIES,
                    delay,
                )
                last_exc = exc
                await asyncio.sleep(delay)
                continue
            raise
        except Exception:
            raise
    # Should not reach here, but satisfy the type checker.
    assert last_exc is not None
    raise last_exc


async def search_single(
    *,
    query: str,
    config: LeanExploreConfig | None = None,
) -> SearchResponse:
    """Search LeanExplore for a single query.

    Used by the per-concept targeted search in the verification layer.
    Each call creates a fresh ApiClient. This is acceptable for the small
    number of targeted queries per run (typically < 100).

    Retries on transient 5xx errors (up to MAX_RETRIES times with backoff).
    Returns an empty SearchResponse on persistent API errors rather than
    crashing, since targeted queries may hit edge cases.
    """
    cfg = config or LeanExploreConfig()
    client = ApiClient(api_key=cfg.api_key)
    try:
        response = await _search_with_retry(
            client,
            query,
            cfg.limit,
            cfg.packages,
        )
    except Exception as exc:
        logger.warning("LeanExplore search failed for query %r: %s", query, exc)
        return SearchResponse(
            query=query,
            results=[],
            count=0,
            processing_time_ms=None,
        )
    results = [SearchResult.from_lean_explore(item) for item in response.results]
    return SearchResponse(
        query=response.query,
        results=results,
        count=response.count,
        processing_time_ms=response.processing_time_ms,
    )


async def search_queries(
    *,
    queries: Iterable[str],
    config: LeanExploreConfig | None = None,
) -> list[SearchResponse]:
    """Batch search for a list of queries (used for theme-level search).

    Runs queries sequentially. Each query retries on transient 5xx errors.
    If a query fails after all retries, it returns an empty SearchResponse
    rather than aborting the entire batch. This prevents a single flaky
    query from losing all other results.
    """
    cfg = config or LeanExploreConfig()
    client = ApiClient(api_key=cfg.api_key)
    responses: list[SearchResponse] = []
    for query in queries:
        try:
            response = await _search_with_retry(
                client,
                query,
                cfg.limit,
                cfg.packages,
            )
        except Exception as exc:
            logger.warning(
                "LeanExplore search failed for theme query %r: %s", query, exc
            )
            responses.append(
                SearchResponse(
                    query=query,
                    results=[],
                    count=0,
                    processing_time_ms=None,
                )
            )
            continue
        results = [SearchResult.from_lean_explore(item) for item in response.results]
        responses.append(
            SearchResponse(
                query=response.query,
                results=results,
                count=response.count,
                processing_time_ms=response.processing_time_ms,
            )
        )
    return responses
