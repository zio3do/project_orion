"""
Decomposer — Stage 1 of the Library Architect pipeline.

Takes a mathematical theme (name + optional document) and produces a raw
decomposition of definitions and lemma sketches.

Uses a two-pass LLM architecture:
  Pass 1 (Skeleton): One LLM call produces a lightweight plan — just names,
    one-line descriptions, layer assignments, and dependency links. This
    separates the "what to include" planning decision from verbose JSON
    generation, allowing the LLM to produce 15-25 items without hitting
    its output length ceiling (~5000-6000 chars).
  Pass 2 (Expansion): Batched LLM calls expand each item with full details
    — Lean signatures, search queries, proof hints, difficulty ratings.
    Items are batched in groups of ~6 to stay within comfortable output
    bounds per call.

The expansion pass can optionally receive grounding context (Mathlib source
snippets from LeanExplore) and oracle exemplars (proven Lean 4 files from
the repo). When provided, these are injected into the expansion prompt to
ground the LLM's signatures in real Mathlib API usage, addressing syntax
and typeclass errors that arise from the LLM working from memory alone.

Caching: Both passes are cached to disk so re-runs skip expensive LLM calls.
Cache is keyed by SHA-256 of (theme + theme_doc + model) for the skeleton,
and by the skeleton content + grounding context for expansion batches.
"""

from __future__ import annotations

import hashlib
import json
import logging
import sys
from pathlib import Path
from typing import Any

from library_architect.models import (
    Decomposition,
    DefinitionSketch,
    GroundedDecomposition,
    LemmaSketch,
)

# Reuse the Edge Finder's LLM client — same retry/truncation logic.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "edge_finder"))
from edge_finder.llm.client import LlmClient

logger = logging.getLogger(__name__)

_PROMPTS_DIR = Path(__file__).resolve().parent / "prompts"
_CACHE_DIR = Path("library_architect/.cache/decomposition")

# How many items to expand per LLM call in Pass 2.
EXPANSION_BATCH_SIZE = 6


# ---------------------------------------------------------------------------
# Prompt loading
# ---------------------------------------------------------------------------

def _load_prompt(name: str) -> str:
    """Load a prompt template from the prompts directory."""
    return (_PROMPTS_DIR / name).read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Cache helpers
# ---------------------------------------------------------------------------

def _cache_key(*parts: str) -> str:
    """Deterministic cache key from arbitrary string parts."""
    raw = "|".join(parts)
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def _load_cached(key: str) -> dict[str, Any] | None:
    """Load cached JSON data, or None if not cached."""
    path = _CACHE_DIR / f"{key}.json"
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        logger.debug("Cache read failed for %s: %s", key, exc)
        return None


def _save_to_cache(key: str, data: dict[str, Any]) -> None:
    """Persist JSON data to disk cache."""
    try:
        _CACHE_DIR.mkdir(parents=True, exist_ok=True)
        path = _CACHE_DIR / f"{key}.json"
        path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    except Exception as exc:
        logger.debug("Cache write failed for %s: %s", key, exc)


# ---------------------------------------------------------------------------
# JSON parsing helpers
# ---------------------------------------------------------------------------

def _strip_fences(text: str) -> str:
    """Strip markdown code fences if present."""
    text = text.strip()
    if text.startswith("```"):
        first_newline = text.index("\n")
        text = text[first_newline + 1:]
    if text.endswith("```"):
        text = text[:-3].rstrip()
    return text


# ---------------------------------------------------------------------------
# Oracle exemplar loading
# ---------------------------------------------------------------------------

def _find_oracle_exemplars(theme_doc: str | None) -> list[dict[str, str]]:
    """Find oracle test files referenced in the theme document.

    Scans the theme document for file paths matching Orion/OracleTests/*.lean,
    reads them from disk, and returns them as name+content pairs.

    Returns at most 5 exemplars to avoid overwhelming the prompt.
    """
    if not theme_doc:
        return []

    import re
    # Match paths like Orion/OracleTests/LevelCardSum.lean
    pattern = r'(?:Orion/OracleTests/\w+\.lean)'
    matches = re.findall(pattern, theme_doc)
    if not matches:
        return []

    # Deduplicate while preserving order.
    seen: set[str] = set()
    unique: list[str] = []
    for m in matches:
        if m not in seen:
            seen.add(m)
            unique.append(m)

    exemplars: list[dict[str, str]] = []
    project_root = Path(__file__).resolve().parent.parent
    for rel_path in unique[:5]:
        full_path = project_root / rel_path
        if full_path.exists():
            content = full_path.read_text(encoding="utf-8")
            exemplars.append({
                "file": rel_path,
                "content": content,
            })
        else:
            logger.debug("Oracle test file not found: %s", full_path)

    return exemplars


# ---------------------------------------------------------------------------
# Grounding context collection
# ---------------------------------------------------------------------------

def _collect_grounding_context(
    grounded: GroundedDecomposition | None,
    batch_names: list[str],
) -> str:
    """Collect Mathlib source snippets relevant to a batch of items.

    Extracts source_text from grounding results for items in the batch,
    deduplicates by declaration name, and formats as a prompt section.

    Returns an empty string if no grounding data is available.
    """
    if grounded is None:
        return ""

    # Build lookup: item name → source snippets.
    snippets_by_item: dict[str, list[dict[str, str]]] = {}
    for gd in grounded.definitions:
        if gd.sketch.name in batch_names and gd.grounding.source_snippets:
            snippets_by_item[gd.sketch.name] = gd.grounding.source_snippets
    for gl in grounded.lemmas:
        if gl.sketch.name in batch_names and gl.grounding.source_snippets:
            snippets_by_item[gl.sketch.name] = gl.grounding.source_snippets

    if not snippets_by_item:
        return ""

    # Deduplicate across all items in the batch.
    seen_names: set[str] = set()
    unique_snippets: list[dict[str, str]] = []
    for item_name in batch_names:
        for snippet in snippets_by_item.get(item_name, []):
            sname = snippet.get("name", "")
            if sname and sname not in seen_names:
                seen_names.add(sname)
                unique_snippets.append(snippet)

    if not unique_snippets:
        return ""

    # Limit total snippets to avoid overwhelming the prompt.
    unique_snippets = unique_snippets[:10]

    lines = [
        "\n## Mathlib Source Context (from LeanExplore)\n",
        "The following are real Lean 4 declarations from Mathlib that are related to the items ",
        "you are expanding. Use these as ground truth for API names, typeclass patterns, ",
        "and calling conventions. Your signatures MUST be consistent with these patterns.\n",
    ]
    for s in unique_snippets:
        lines.append(f"\n### `{s['name']}`\n")
        lines.append(f"```lean\n{s['source_text'].strip()}\n```\n")

    return "".join(lines)


# ---------------------------------------------------------------------------
# Pass 1: Skeleton
# ---------------------------------------------------------------------------

def _build_skeleton_prompt(theme: str, theme_doc: str | None) -> str:
    """Build the prompt for Pass 1 (skeleton generation)."""
    system = _load_prompt("decomposer_skeleton_prompt.md")
    parts = [
        system,
        "\n---\n",
        f"## Theme: {theme}\n",
    ]
    if theme_doc:
        parts.append("\n## Theme Document\n\n")
        parts.append(theme_doc)
        parts.append("\n")
    parts.append("\n---\n")
    parts.append(
        "Now produce the JSON skeleton for this theme. "
        "Return only the JSON object, no other text.\n"
    )
    return "".join(parts)


def _run_skeleton_pass(
    theme: str,
    theme_doc: str | None,
    client: LlmClient,
    *,
    use_cache: bool = True,
    model: str = "gpt-4o",
) -> dict[str, Any]:
    """Pass 1: Generate a lightweight skeleton of definitions and lemmas.

    Returns the raw parsed JSON dict (not yet converted to model objects,
    because Pass 2 needs to augment it first).
    """
    cache_key = _cache_key("skeleton", theme, theme_doc or "", model)

    if use_cache:
        cached = _load_cached(cache_key)
        if cached is not None:
            n_defs = len(cached.get("definitions", []))
            n_lemmas = len(cached.get("lemmas", []))
            print(f"  [decomposer] Skeleton loaded from cache "
                  f"({n_defs} defs, {n_lemmas} lemmas)")
            return cached

    prompt = _build_skeleton_prompt(theme, theme_doc)
    raw = client.complete_json(prompt)
    text = _strip_fences(raw)
    if not text:
        raise RuntimeError(
            "Skeleton LLM call returned empty response. "
            "Check API key and model availability."
        )
    data = json.loads(text)

    n_defs = len(data.get("definitions", []))
    n_lemmas = len(data.get("lemmas", []))
    print(f"  [decomposer] Skeleton generated: {n_defs} defs, {n_lemmas} lemmas")

    if use_cache:
        _save_to_cache(cache_key, data)

    return data


# ---------------------------------------------------------------------------
# Pass 2: Expansion (grounding-aware)
# ---------------------------------------------------------------------------

def _build_expansion_prompt(
    theme: str,
    theme_doc: str | None,
    skeleton: dict[str, Any],
    batch_items: list[dict[str, Any]],
    *,
    grounding_context: str = "",
    oracle_exemplars: list[dict[str, str]] | None = None,
) -> str:
    """Build the prompt for Pass 2 (expanding a batch of skeleton items).

    Includes the full skeleton for context (so the LLM knows the global
    plan and can write consistent signatures), but only asks for expansion
    of the specific batch items.

    When grounding_context is provided, it is appended as a section containing
    real Mathlib source code from LeanExplore — grounding the LLM in actual
    API names, typeclass patterns, and calling conventions.

    When oracle_exemplars are provided, they are appended as proven Lean 4
    files that demonstrate correct signature patterns for this theme.
    """
    system = _load_prompt("decomposer_expand_prompt.md")

    # Compact skeleton summary for context.
    skeleton_summary = json.dumps({
        "theme": skeleton.get("theme", theme),
        "layers": skeleton.get("layers", []),
        "definitions": [
            {"name": d["name"], "informal": d.get("informal", ""), "layer": d.get("layer", "")}
            for d in skeleton.get("definitions", [])
        ],
        "lemmas": [
            {"name": l["name"], "informal_statement": l.get("informal_statement", ""),
             "layer": l.get("layer", ""), "depends_on": l.get("depends_on", [])}
            for l in skeleton.get("lemmas", [])
        ],
    }, indent=2)

    # The specific items to expand.
    batch_json = json.dumps(batch_items, indent=2)

    parts = [
        system,
        "\n---\n",
        f"## Theme: {theme}\n",
    ]
    if theme_doc:
        parts.append("\n## Theme Document\n\n")
        parts.append(theme_doc)
        parts.append("\n")

    # Oracle exemplars — proven Lean 4 files as ground truth.
    if oracle_exemplars:
        parts.append("\n## Oracle Exemplars (Proven Lean 4 — Ground Truth)\n\n")
        parts.append(
            "The following files contain **proven** Lean 4 code for this theme. "
            "These are the authoritative source of truth for correct signatures, "
            "typeclass assumptions, and API usage. Your generated signatures MUST "
            "be consistent with the patterns demonstrated here.\n"
        )
        for ex in oracle_exemplars:
            parts.append(f"\n### `{ex['file']}`\n\n")
            parts.append(f"```lean\n{ex['content'].strip()}\n```\n")

    # Grounding context — Mathlib source from LeanExplore.
    if grounding_context:
        parts.append(grounding_context)

    parts.append("\n## Full Skeleton (for context)\n\n```json\n")
    parts.append(skeleton_summary)
    parts.append("\n```\n")
    parts.append("\n## Items to Expand\n\n")
    parts.append("Expand the following items with full Lean 4 signatures, ")
    parts.append("search queries, hints, and difficulty:\n\n```json\n")
    parts.append(batch_json)
    parts.append("\n```\n")
    parts.append("\n---\n")
    parts.append(
        "Now produce the JSON expansion for these items. "
        "Return only the JSON object, no other text.\n"
    )
    return "".join(parts)


def _run_expansion_pass(
    theme: str,
    theme_doc: str | None,
    skeleton: dict[str, Any],
    client: LlmClient,
    *,
    grounded: GroundedDecomposition | None = None,
    oracle_exemplars: list[dict[str, str]] | None = None,
    use_cache: bool = True,
    model: str = "gpt-4o",
) -> dict[str, dict[str, Any]]:
    """Pass 2: Expand skeleton items with full details, in batches.

    When grounded is provided, Mathlib source snippets from LeanExplore are
    injected into each batch's expansion prompt to ground signatures in real
    API usage.

    When oracle_exemplars are provided, proven Lean 4 files are included as
    authoritative examples of correct signature patterns.

    Returns a dict mapping item names to their expanded details.
    """
    # Collect all items to expand, tagged with their type.
    all_items: list[dict[str, Any]] = []
    for d in skeleton.get("definitions", []):
        all_items.append({
            "name": d["name"],
            "type": "definition",
            "informal": d.get("informal", ""),
            "layer": d.get("layer", ""),
            "depends_on": d.get("depends_on", []),
        })
    for l in skeleton.get("lemmas", []):
        all_items.append({
            "name": l["name"],
            "type": "lemma",
            "informal_statement": l.get("informal_statement", ""),
            "layer": l.get("layer", ""),
            "depends_on": l.get("depends_on", []),
        })

    # Split into batches.
    batches: list[list[dict[str, Any]]] = []
    for i in range(0, len(all_items), EXPANSION_BATCH_SIZE):
        batches.append(all_items[i : i + EXPANSION_BATCH_SIZE])

    # Expand each batch.
    expanded: dict[str, dict[str, Any]] = {}
    skeleton_json = json.dumps(skeleton, sort_keys=True)

    # Include a grounding fingerprint in the cache key so that re-runs with
    # new grounding data produce fresh expansions.
    grounding_fingerprint = ""
    if grounded is not None:
        snippet_count = sum(
            len(gd.grounding.source_snippets) for gd in grounded.definitions
        ) + sum(
            len(gl.grounding.source_snippets) for gl in grounded.lemmas
        )
        grounding_fingerprint = f"grounded:{snippet_count}"

    oracle_fingerprint = ""
    if oracle_exemplars:
        oracle_fingerprint = f"oracle:{len(oracle_exemplars)}"

    for batch_idx, batch in enumerate(batches):
        batch_names = [item["name"] for item in batch]
        batch_key = _cache_key(
            "expand_v2", model, skeleton_json,
            json.dumps(batch_names, sort_keys=True),
            grounding_fingerprint,
            oracle_fingerprint,
        )

        # Check cache.
        if use_cache:
            cached = _load_cached(batch_key)
            if cached is not None:
                print(f"  [decomposer] Expansion batch {batch_idx + 1}/{len(batches)} "
                      f"loaded from cache ({len(cached.get('items', []))} items)")
                for item in cached.get("items", []):
                    expanded[item["name"]] = item
                continue

        # Build grounding context for this specific batch.
        grounding_ctx = _collect_grounding_context(grounded, batch_names)

        print(f"  [decomposer] Expanding batch {batch_idx + 1}/{len(batches)} "
              f"({len(batch)} items: {', '.join(batch_names)})"
              f"{' [with grounding]' if grounding_ctx else ''}"
              f"{' [with exemplars]' if oracle_exemplars else ''}...")

        # Retry expansion up to 2 times on empty/failed responses.
        items: list[dict[str, Any]] = []
        batch_data: dict[str, Any] = {}
        for attempt in range(3):
            prompt = _build_expansion_prompt(
                theme, theme_doc, skeleton, batch,
                grounding_context=grounding_ctx,
                oracle_exemplars=oracle_exemplars,
            )
            raw = client.complete_json(prompt)
            text = _strip_fences(raw)
            if not text:
                logger.warning(
                    "Expansion batch %d/%d attempt %d returned empty response",
                    batch_idx + 1, len(batches), attempt + 1,
                )
                continue
            try:
                batch_data = json.loads(text)
                items = batch_data.get("items", [])
                if items:
                    break
            except json.JSONDecodeError as exc:
                logger.warning(
                    "Expansion batch %d/%d attempt %d JSON parse error: %s",
                    batch_idx + 1, len(batches), attempt + 1, exc,
                )
                continue

        if not items:
            print(f"  [decomposer]   -> WARNING: all attempts failed, skipping batch")
            continue
        for item in items:
            expanded[item["name"]] = item

        if use_cache:
            _save_to_cache(batch_key, batch_data)

        print(f"  [decomposer]   -> expanded {len(items)} items")

    return expanded


# ---------------------------------------------------------------------------
# Merging skeleton + expansion
# ---------------------------------------------------------------------------

def _merge_into_decomposition(
    theme: str,
    skeleton: dict[str, Any],
    expanded: dict[str, dict[str, Any]],
) -> Decomposition:
    """Merge Pass 1 skeleton with Pass 2 expansions into a Decomposition.

    For any item missing from expansion (e.g., LLM omitted it), we still
    include it with skeleton-only data and empty expansion fields.
    """
    definitions: list[DefinitionSketch] = []
    lemmas: list[LemmaSketch] = []

    for d in skeleton.get("definitions", []):
        name = d["name"]
        exp = expanded.get(name, {})
        definitions.append(DefinitionSketch(
            name=name,
            informal=d.get("informal", ""),
            suggested_signature=exp.get("suggested_signature", ""),
            layer=d.get("layer", ""),
            depends_on=d.get("depends_on", []),
            mathlib_search_queries=exp.get("mathlib_search_queries", []),
        ))

    for l in skeleton.get("lemmas", []):
        name = l["name"]
        exp = expanded.get(name, {})
        lemmas.append(LemmaSketch(
            name=name,
            informal_statement=l.get("informal_statement", ""),
            suggested_signature=exp.get("suggested_signature", ""),
            depends_on=l.get("depends_on", []),
            layer=l.get("layer", ""),
            hints=exp.get("hints", ""),
            difficulty=exp.get("difficulty", "medium"),
            mathlib_search_queries=exp.get("mathlib_search_queries", []),
        ))

    layers = skeleton.get("layers", [])

    return Decomposition(
        theme=theme,
        definitions=definitions,
        lemmas=lemmas,
        layers=layers,
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def skeleton_pass(
    theme: str,
    theme_doc: str | None = None,
    *,
    model: str = "gpt-4o",
    use_cache: bool = True,
) -> dict[str, Any]:
    """Run Pass 1 only: generate a lightweight skeleton.

    Returns the raw skeleton dict (definitions + lemmas + layers + deps).
    This is used by the new pipeline flow where grounding happens between
    skeleton and expansion.
    """
    client = LlmClient(model=model)
    return _run_skeleton_pass(
        theme, theme_doc, client,
        use_cache=use_cache, model=model,
    )


def expand_with_grounding(
    theme: str,
    skeleton: dict[str, Any],
    theme_doc: str | None = None,
    *,
    grounded: GroundedDecomposition | None = None,
    oracle_exemplars: list[dict[str, str]] | None = None,
    model: str = "gpt-4o",
    use_cache: bool = True,
) -> Decomposition:
    """Run Pass 2 with grounding context: expand skeleton items with full details.

    This is the grounding-aware expansion that injects Mathlib source snippets
    and oracle exemplars into the expansion prompt.

    Args:
        theme: The theme name.
        skeleton: Raw skeleton dict from skeleton_pass().
        theme_doc: Optional theme document markdown.
        grounded: Optional GroundedDecomposition with source snippets.
        oracle_exemplars: Optional list of {file, content} dicts for proven Lean 4.
        model: OpenAI model to use.
        use_cache: Whether to use disk cache.

    Returns:
        A Decomposition with expanded signatures, hints, and queries.
    """
    if oracle_exemplars is None:
        oracle_exemplars = _find_oracle_exemplars(theme_doc)

    client = LlmClient(model=model)
    expanded = _run_expansion_pass(
        theme, theme_doc, skeleton, client,
        grounded=grounded,
        oracle_exemplars=oracle_exemplars,
        use_cache=use_cache, model=model,
    )
    return _merge_into_decomposition(theme, skeleton, expanded)


def decompose(
    theme: str,
    theme_doc: str | None = None,
    *,
    model: str = "gpt-4o",
    use_cache: bool = True,
) -> Decomposition:
    """Decompose a mathematical theme into definitions and lemma sketches.

    Convenience wrapper that runs both passes without grounding context.
    For the grounding-aware pipeline, use skeleton_pass() + ground() +
    expand_with_grounding() instead.

    Args:
        theme: The theme name (e.g., "Graded Order Combinatorics").
        theme_doc: Optional markdown document describing the theme.
        model: OpenAI model to use for decomposition.
        use_cache: Whether to use disk cache for LLM responses.

    Returns:
        A Decomposition containing ungrounded definition and lemma sketches.
    """
    client = LlmClient(model=model)

    # Pass 1: Skeleton.
    skeleton = _run_skeleton_pass(
        theme, theme_doc, client,
        use_cache=use_cache, model=model,
    )

    # Pass 2: Expansion (without grounding).
    expanded = _run_expansion_pass(
        theme, theme_doc, skeleton, client,
        use_cache=use_cache, model=model,
    )

    # Merge into final Decomposition.
    return _merge_into_decomposition(theme, skeleton, expanded)
