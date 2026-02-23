"""
pre_search.py — Pre-search step for the Proof Oracle.

Responsibility: Before spawning a Claude Code session, generate targeted
LeanExplore search queries and run them to produce relevant Mathlib context.
This context is injected into the proof agent prompt so the agent starts
warm — it already knows which Mathlib declarations are likely relevant.

Architecture:
  1. Query generation: A cheap Anthropic API call (Claude Haiku) takes
     the lemma spec and produces 3-5 search queries optimized for
     LeanExplore's semantic search.
  2. LeanExplore search: Run each query against the LeanExplore API,
     collect results, deduplicate by declaration name.
  3. Formatting: Produce a markdown-formatted context block that gets
     inserted into the proof agent prompt.

Cost: ~$0.01 for query generation (Sonnet 4) + negligible for LeanExplore API
calls. This is ~50x cheaper than the agent spending 3-5 turns doing its own search.
"""

from __future__ import annotations

import asyncio
import json
import logging
import os
from dataclasses import dataclass
from pathlib import Path

import httpx

logger = logging.getLogger(__name__)

# Models for query generation. Sonnet is used because the API key only has
# access to claude-sonnet-4. Cost is still negligible (~$0.01) vs. agent sessions.
QUERY_GEN_MODEL = "claude-sonnet-4-20250514"
QUERY_GEN_MAX_TOKENS = 512
QUERY_GEN_TEMPERATURE = 0.0
ANTHROPIC_API_URL = "https://api.anthropic.com/v1/messages"

# LeanExplore search parameters
RESULTS_PER_QUERY = 5  # Top results to keep per query (API may return more)
MAX_QUERIES = 5
MAX_TOTAL_RESULTS = 15  # Hard cap on total unique declarations

# Prompt for generating search queries
QUERY_GEN_SYSTEM_PROMPT = """\
You are a Lean 4 / Mathlib expert. Given a theorem specification, generate \
search queries for the LeanExplore API to find relevant Mathlib declarations.

LeanExplore uses semantic search — queries should be natural language \
descriptions of mathematical concepts, not Lean syntax.

Generate 3-5 queries that would find:
1. Existing theorems that are identical or closely related to the target
2. Key definitions and lemmas the proof will likely need
3. Useful tactics or automation lemmas for the proof domain

Output ONLY a JSON array of strings. No explanation, no markdown fences."""

QUERY_GEN_USER_TEMPLATE = """\
Theorem to prove:
  Name: {lemma_name}
  Statement: {informal_statement}
  Lean signature: {suggested_signature}
  Dependencies: {depends_on}

Generate search queries for LeanExplore to find relevant Mathlib declarations."""


@dataclass
class PreSearchResult:
    """Result of the pre-search step."""

    queries: list[str]
    context_block: str  # Formatted markdown for prompt injection
    declarations_found: int
    cost_usd: float  # Cost of the query generation LLM call


def _build_env_from_dotenv(project_root: Path) -> dict[str, str]:
    """Load .env file and return key-value pairs (reuses session.py pattern)."""
    env: dict[str, str] = {}
    dotenv_path = project_root / ".env"
    if dotenv_path.exists():
        for line in dotenv_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "=" in line:
                key, _, value = line.partition("=")
                env[key.strip()] = value.strip()
    return env


def _get_api_keys(project_root: Path) -> tuple[str, str]:
    """
    Get Anthropic and LeanExplore API keys from environment or .env file.

    Returns:
        (anthropic_api_key, leanexplore_api_key)

    Raises:
        ValueError if either key is missing.
    """
    dotenv = _build_env_from_dotenv(project_root)

    anthropic_key = (
        os.environ.get("ANTHROPIC_API_KEY")
        or os.environ.get("CLAUDE_API_KEY")
        or dotenv.get("ANTHROPIC_API_KEY")
        or dotenv.get("CLAUDE_API_KEY")
        or ""
    )
    leanexplore_key = (
        os.environ.get("LEANEXPLORE_API_KEY") or dotenv.get("LEANEXPLORE_API_KEY") or ""
    )

    if not anthropic_key:
        raise ValueError(
            "No Anthropic API key found. Set ANTHROPIC_API_KEY or "
            "CLAUDE_API_KEY in environment or .env file."
        )
    if not leanexplore_key:
        raise ValueError(
            "No LeanExplore API key found. Set LEANEXPLORE_API_KEY "
            "in environment or .env file."
        )

    return anthropic_key, leanexplore_key


async def _generate_queries(
    anthropic_key: str,
    lemma_name: str,
    informal_statement: str,
    suggested_signature: str,
    depends_on: list[str],
) -> tuple[list[str], float]:
    """
    Use a cheap Anthropic model to generate LeanExplore search queries.

    Returns:
        (list of query strings, cost in USD)
    """
    user_message = QUERY_GEN_USER_TEMPLATE.format(
        lemma_name=lemma_name,
        informal_statement=informal_statement,
        suggested_signature=suggested_signature,
        depends_on=", ".join(depends_on) if depends_on else "(none)",
    )

    payload = {
        "model": QUERY_GEN_MODEL,
        "max_tokens": QUERY_GEN_MAX_TOKENS,
        "temperature": QUERY_GEN_TEMPERATURE,
        "system": QUERY_GEN_SYSTEM_PROMPT,
        "messages": [{"role": "user", "content": user_message}],
    }

    headers = {
        "x-api-key": anthropic_key,
        "anthropic-version": "2023-06-01",
        "content-type": "application/json",
    }

    async with httpx.AsyncClient(timeout=30.0) as client:
        response = await client.post(ANTHROPIC_API_URL, json=payload, headers=headers)
        response.raise_for_status()
        data = response.json()

    # Extract text from response
    text = ""
    for block in data.get("content", []):
        if block.get("type") == "text":
            text += block.get("text", "")

    # Calculate cost (Sonnet 4 pricing: $3/MTok input, $15/MTok output)
    usage = data.get("usage", {})
    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cost = (input_tokens * 3.0 + output_tokens * 15.0) / 1_000_000

    # Parse the JSON array of queries
    try:
        # Strip markdown fences if the model added them despite instructions
        cleaned = text.strip()
        if cleaned.startswith("```"):
            cleaned = cleaned.split("\n", 1)[1] if "\n" in cleaned else cleaned
            if cleaned.endswith("```"):
                cleaned = cleaned[: -len("```")]
            cleaned = cleaned.strip()

        queries = json.loads(cleaned)
        if not isinstance(queries, list):
            raise ValueError("Expected a JSON array")
        queries = [str(q) for q in queries[:MAX_QUERIES]]
    except (json.JSONDecodeError, ValueError) as e:
        logger.warning(
            "Failed to parse query generation output as JSON: %s. "
            "Falling back to keyword extraction. Raw output: %s",
            e,
            text[:200],
        )
        # Fallback: use the lemma name and informal statement as queries
        queries = [lemma_name.replace("_", " "), informal_statement[:100]]

    logger.info("Generated %d search queries (cost: $%.4f)", len(queries), cost)
    for i, q in enumerate(queries):
        logger.info("  Query %d: %s", i + 1, q)

    return queries, cost


async def _search_leanexplore(
    leanexplore_key: str,
    queries: list[str],
) -> list[dict]:
    """
    Run search queries against LeanExplore API and collect results.

    Returns a deduplicated list of declaration dicts with keys:
    name, module, source_text, docstring, informalization.
    """
    from lean_explore.api import ApiClient

    client = ApiClient(api_key=leanexplore_key)

    seen_names: set[str] = set()
    results: list[dict] = []

    for query in queries:
        if len(results) >= MAX_TOTAL_RESULTS:
            break
        try:
            response = await client.search(
                query=query,
                limit=RESULTS_PER_QUERY,
                packages=["Mathlib"],
            )
            # API may ignore limit param; slice client-side
            for r in response.results[:RESULTS_PER_QUERY]:
                if r.name not in seen_names:
                    seen_names.add(r.name)
                    results.append(
                        {
                            "name": r.name,
                            "module": r.module,
                            "source_text": r.source_text,
                            "docstring": r.docstring or "",
                            "informalization": r.informalization or "",
                        }
                    )
                    if len(results) >= MAX_TOTAL_RESULTS:
                        break
        except Exception as e:
            logger.warning("LeanExplore search failed for query %r: %s", query, e)
            continue

    logger.info(
        "LeanExplore returned %d unique declarations from %d queries",
        len(results),
        len(queries),
    )
    return results


def _format_context_block(results: list[dict]) -> str:
    """
    Format LeanExplore results into a markdown block for prompt injection.

    Each result shows: name, module, source, and a brief description.
    This is what the proof agent sees as pre-loaded Mathlib context.
    """
    if not results:
        return "(No relevant Mathlib declarations found by pre-search.)"

    lines = []
    for i, r in enumerate(results, 1):
        lines.append(f"### {i}. `{r['name']}`")
        lines.append(f"**Module:** `{r['module']}`")
        if r["informalization"]:
            lines.append(f"**Description:** {r['informalization']}")
        if r["docstring"]:
            lines.append(f"**Docstring:** {r['docstring']}")
        lines.append(f"```lean\n{r['source_text']}\n```")
        lines.append("")

    return "\n".join(lines)


async def _run_pre_search_async(
    lemma_name: str,
    informal_statement: str,
    suggested_signature: str,
    depends_on: list[str],
    project_root: Path,
) -> PreSearchResult:
    """Async implementation of the pre-search step."""
    anthropic_key, leanexplore_key = _get_api_keys(project_root)

    # Phase 1: Generate search queries
    queries, cost = await _generate_queries(
        anthropic_key=anthropic_key,
        lemma_name=lemma_name,
        informal_statement=informal_statement,
        suggested_signature=suggested_signature,
        depends_on=depends_on,
    )

    # Phase 2: Run LeanExplore searches
    results = await _search_leanexplore(leanexplore_key, queries)

    # Phase 3: Format context
    context_block = _format_context_block(results)

    return PreSearchResult(
        queries=queries,
        context_block=context_block,
        declarations_found=len(results),
        cost_usd=cost,
    )


def run_pre_search(
    lemma_name: str,
    informal_statement: str,
    suggested_signature: str,
    depends_on: list[str],
    project_root: Path,
) -> PreSearchResult:
    """
    Run the pre-search step synchronously.

    This is the public API called by the orchestrator. It generates
    search queries via a cheap LLM call, runs them against LeanExplore,
    and returns formatted Mathlib context for prompt injection.

    Args:
        lemma_name: The name of the lemma to prove.
        informal_statement: Natural language description.
        suggested_signature: Lean 4 type signature.
        depends_on: List of dependency names.
        project_root: Project root (for .env loading).

    Returns:
        PreSearchResult with context block and metadata.
    """
    return asyncio.run(
        _run_pre_search_async(
            lemma_name=lemma_name,
            informal_statement=informal_statement,
            suggested_signature=suggested_signature,
            depends_on=depends_on,
            project_root=project_root,
        )
    )
