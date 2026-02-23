"""Edge Finder CLI orchestrator.

This module is the main entry point for the edge finder pipeline. It parses
command-line arguments, loads environment variables, and runs the full pipeline:
concept generation -> LeanExplore search -> concept re-mapping (Iteration 5) ->
per-concept verification (pass 1: theme-level, pass 2: targeted) -> density
analysis -> gap classification -> pocket synthesis -> output writing. It also
supports a dry-run mode that skips LLM calls and uses cached inputs for cheaper
iteration on the analysis logic.
"""

from __future__ import annotations

import argparse
import asyncio
import json
from datetime import datetime
import os
from pathlib import Path

from edge_finder.analysis.candidates import rank_candidates
from edge_finder.analysis.density import compute_density_report
from edge_finder.analysis.heuristics import classify_gaps
from edge_finder.config import DEFAULT_OUTPUT_DIR, build_metadata
from edge_finder.llm.concept_generator import generate_concepts
from edge_finder.llm.concept_remapper import remap_concepts
from edge_finder.llm.concept_rewriter import rewrite_concepts
from edge_finder.llm.pocket_synthesis import synthesize_pocket
from edge_finder.output.writer import write_run_report
from edge_finder.search.leanexplore import (
    LeanExploreConfig,
    search_queries,
    search_single,
)
from edge_finder.search.logger import log_search_response
from edge_finder.verification import verify_concepts, refine_verification


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Project Orion edge finder")
    parser.add_argument("--theme", required=True, help="Seed theme for the run")
    parser.add_argument(
        "--output-dir",
        default=DEFAULT_OUTPUT_DIR,
        help=f"Directory for run outputs (default: {DEFAULT_OUTPUT_DIR})",
    )
    parser.add_argument(
        "--version",
        default="0.1.0",
        help="Edge finder run version tag",
    )
    parser.add_argument(
        "--model",
        default="gpt-4o-mini",
        help="OpenAI model name",
    )
    parser.add_argument(
        "--search-limit",
        type=int,
        default=20,
        help="LeanExplore result limit per query",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Skip OpenAI calls and use cached inputs",
    )
    parser.add_argument(
        "--concepts-path",
        help="Path to cached concepts.json (required for --dry-run)",
    )
    parser.add_argument(
        "--pocket-path",
        help="Path to cached pocket.json (optional for --dry-run)",
    )
    parser.add_argument(
        "--skip-targeted-search",
        action="store_true",
        help="Skip per-concept targeted queries (Iteration 2 refinement step)",
    )
    parser.add_argument(
        "--skip-remap",
        action="store_true",
        help="Skip LLM concept re-mapping (Iteration 5 grounding step)",
    )
    return parser


def _load_dotenv(path: Path) -> None:
    if not path.exists():
        return
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "=" not in stripped:
            continue
        key, value = stripped.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    _load_dotenv(Path(".env"))

    if not args.dry_run and "OPENAI_API_KEY" not in os.environ:
        raise RuntimeError("OPENAI_API_KEY is required to run the edge finder")
    if "LEANEXPLORE_API_KEY" not in os.environ:
        raise RuntimeError("LEANEXPLORE_API_KEY is required to run the edge finder")

    output_dir = Path(args.output_dir)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
    theme_slug = args.theme.replace(" ", "_").lower()[:80]
    run_dir = output_dir / f"run_{timestamp}_{theme_slug}"
    run_dir.mkdir(parents=True, exist_ok=True)

    if args.dry_run:
        if not args.concepts_path:
            raise RuntimeError("--concepts-path is required when --dry-run is set")
        concepts_path = Path(args.concepts_path)
        if not concepts_path.exists():
            raise RuntimeError(f"Concepts file not found: {concepts_path}")
        concepts = json.loads(concepts_path.read_text(encoding="utf-8"))
    else:
        concepts = generate_concepts(args.theme, model=args.model)
    concepts_path = run_dir / "concepts.json"
    with concepts_path.open("w", encoding="utf-8") as handle:
        json.dump(concepts, handle, ensure_ascii=True, indent=2)

    queries = concepts.get("search_queries", [])
    if not isinstance(queries, list) or not queries:
        raise ValueError("Concept generator returned no search_queries")

    search_config = LeanExploreConfig(
        api_key=os.environ.get("LEANEXPLORE_API_KEY"),
        limit=args.search_limit,
        packages=["Mathlib"],
    )
    responses = asyncio.run(search_queries(queries=queries, config=search_config))

    search_log_path = run_dir / "search_log.jsonl"
    for response in responses:
        log_search_response(search_log_path, response)

    responses_path = run_dir / "search_responses.json"
    with responses_path.open("w", encoding="utf-8") as handle:
        json.dump(
            {"responses": [response.to_dict() for response in responses]},
            handle,
            ensure_ascii=True,
            indent=2,
        )

    # --- Concept re-mapping (Iteration 5: name grounding) ---
    # After search, ask the LLM to re-map generated concept names to actual
    # Mathlib declaration names observed in the search results.
    remap_log: list[dict[str, str]] = []
    if not args.dry_run and not args.skip_remap:
        remapped_concepts, remap_log = remap_concepts(
            concepts, responses, model=args.model
        )
        # Save both original and remapped for auditability.
        remap_path = run_dir / "concepts_remapped.json"
        with remap_path.open("w", encoding="utf-8") as handle:
            json.dump(remapped_concepts, handle, ensure_ascii=True, indent=2)
        remap_log_path = run_dir / "remap_log.json"
        with remap_log_path.open("w", encoding="utf-8") as handle:
            json.dump(remap_log, handle, ensure_ascii=True, indent=2)
        # Use remapped concepts for verification and downstream steps.
        concepts_for_verification = remapped_concepts
    else:
        concepts_for_verification = concepts

    # --- Concept rewriting (Iteration 6: sibling-evidence propagation) ---
    # For concepts the remapper left unchanged (null), check if a sibling
    # concept was successfully remapped. If so, ask the LLM to rewrite
    # the stranded concept using the sibling's Mathlib namespace as evidence.
    if not args.dry_run and not args.skip_remap and remap_log:
        rewritten_concepts, rewrite_log = rewrite_concepts(
            concepts_for_verification, remap_log, responses, model=args.model
        )
        if rewrite_log:
            rewrite_path = run_dir / "concepts_rewritten.json"
            with rewrite_path.open("w", encoding="utf-8") as handle:
                json.dump(rewritten_concepts, handle, ensure_ascii=True, indent=2)
            rewrite_log_path = run_dir / "rewrite_log.json"
            with rewrite_log_path.open("w", encoding="utf-8") as handle:
                json.dump(rewrite_log, handle, ensure_ascii=True, indent=2)
            concepts_for_verification = rewritten_concepts

    # --- Per-concept verification (pass 1: theme-level) ---
    verification_report = verify_concepts(concepts_for_verification, responses)

    # --- Per-concept targeted search (pass 2: refinement) ---
    all_responses = list(responses)  # combined theme + targeted for density analysis
    if not args.skip_targeted_search:

        async def _search_fn(query: str):
            return await search_single(query=query, config=search_config)

        refined_report, targeted_responses = asyncio.run(
            refine_verification(
                verification_report, concepts_for_verification, _search_fn
            )
        )

        # Log targeted search responses.
        for response in targeted_responses:
            log_search_response(search_log_path, response)
            all_responses.append(response)

        verification_report = refined_report

    verification_path = run_dir / "verification.json"
    with verification_path.open("w", encoding="utf-8") as handle:
        json.dump(verification_report.to_dict(), handle, ensure_ascii=True, indent=2)

    density_report = compute_density_report(all_responses)
    gap_report = classify_gaps(
        density_report, verification=verification_report, responses=all_responses
    )

    # --- Module 4: Pocket candidate ranking ---
    candidate_report = rank_candidates(
        verification=verification_report,
        density=density_report,
        gap=gap_report,
        concepts=concepts_for_verification,
        responses=all_responses,
        theme=args.theme,
    )
    candidates_path = run_dir / "candidates.json"
    with candidates_path.open("w", encoding="utf-8") as handle:
        json.dump(candidate_report.to_dict(), handle, ensure_ascii=True, indent=2)

    evidence = {
        "responses": [response.to_dict() for response in all_responses],
        "verification_report": verification_report.to_dict(),
        "density_report": density_report.to_dict(),
        "gap_report": gap_report.to_dict(),
    }
    if args.dry_run and args.pocket_path:
        pocket_path = Path(args.pocket_path)
        if pocket_path.exists():
            pocket = json.loads(pocket_path.read_text(encoding="utf-8"))
        else:
            raise RuntimeError(f"Pocket file not found: {pocket_path}")
    elif args.dry_run:
        pocket = {
            "theme": args.theme,
            "pocket_summary": "dry-run placeholder",
            "proposed_abstractions": [],
            "candidate_lemmas": [],
            "dependency_sketch": [],
            "justification": ["dry-run placeholder"],
            "risk_level": "Low",
            "dry_run": True,
        }
    else:
        pocket = synthesize_pocket(
            theme=args.theme, evidence=evidence, model=args.model
        )
    pocket_path = run_dir / "pocket.json"
    with pocket_path.open("w", encoding="utf-8") as handle:
        json.dump(pocket, handle, ensure_ascii=True, indent=2)

    metadata = build_metadata(args.version)
    output_path = write_run_report(
        theme=args.theme,
        responses=all_responses,
        verification_report=verification_report,
        density_report=density_report,
        gap_report=gap_report,
        output_dir=run_dir,
        metadata=metadata,
    )

    print(output_path)


if __name__ == "__main__":
    main()
