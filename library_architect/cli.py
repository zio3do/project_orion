"""
CLI entry point for the Library Architect.

Usage:
    python -m library_architect "Graded Order Combinatorics" \\
        --theme-doc library_architect/themes/graded_order_combinatorics.md \\
        --output-dir library_architect/runs/graded_order_combinatorics

Pipeline flow (grounding-aware):
    1. Skeleton pass — LLM generates names + one-liners + deps
    2. Skeleton grounding — LeanExplore searches, collects source_text
    3. Grounded expansion — LLM expands with Mathlib source context + oracle exemplars
    4. Full grounding — re-ground expanded items (search queries may differ)
    5. Assembly — DAG sort, LemmaSpec generation, output files
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from library_architect.config import (
    DEFAULT_OUTPUT_DIR,
    DECOMPOSER_MODEL,
    build_metadata,
)
from library_architect.decomposer import (
    skeleton_pass,
    expand_with_grounding,
    decompose,
)
from library_architect.grounder import ground, ground_skeleton
from library_architect.assembler import assemble


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        prog="library_architect",
        description="Decompose a mathematical theme into a mini-library blueprint.",
    )
    parser.add_argument(
        "theme",
        type=str,
        help="Theme name (e.g., 'Graded Order Combinatorics')",
    )
    parser.add_argument(
        "--theme-doc",
        type=str,
        default=None,
        help="Path to theme document (markdown).",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help=f"Output directory for blueprint files. Defaults to {DEFAULT_OUTPUT_DIR}/<theme_slug>/",
    )
    parser.add_argument(
        "--model",
        type=str,
        default=DECOMPOSER_MODEL,
        help=f"OpenAI model for decomposition. Default: {DECOMPOSER_MODEL}",
    )
    parser.add_argument(
        "--skip-grounding",
        action="store_true",
        help="Skip LeanExplore grounding (for testing without API key).",
    )
    parser.add_argument(
        "--no-cache",
        action="store_true",
        help="Disable disk cache for decomposition and grounding.",
    )
    parser.add_argument(
        "--clear-cache",
        action="store_true",
        help="Clear all cached data before running.",
    )
    parser.add_argument(
        "--legacy",
        action="store_true",
        help="Use legacy pipeline (expansion before grounding, no source context).",
    )
    parser.add_argument(
        "--check-signatures",
        action="store_true",
        help="Run sorry-elaboration check on generated signatures (requires lake).",
    )

    args = parser.parse_args(argv)

    # Handle --clear-cache.
    if args.clear_cache:
        import shutil
        cache_root = Path("library_architect/.cache")
        if cache_root.exists():
            shutil.rmtree(cache_root)
            print(f"Cleared cache: {cache_root}")
        else:
            print("No cache to clear.")

    theme: str = args.theme
    theme_doc: str | None = None
    theme_doc_path: str | None = args.theme_doc

    if theme_doc_path:
        p = Path(theme_doc_path)
        if not p.exists():
            print(f"Error: theme document not found: {theme_doc_path}", file=sys.stderr)
            sys.exit(1)
        theme_doc = p.read_text(encoding="utf-8")

    # Determine output directory.
    if args.output_dir:
        output_dir = Path(args.output_dir)
    else:
        slug = theme.lower().replace(" ", "_")
        output_dir = Path(DEFAULT_OUTPUT_DIR) / slug

    use_cache = not args.no_cache

    metadata = build_metadata()
    print(f"Library Architect v{metadata.version}")
    print(f"Theme: {theme}")
    print(f"Output: {output_dir}")
    if not use_cache:
        print("Cache: disabled")
    if args.legacy:
        print("Mode: legacy (expansion before grounding)")
    else:
        print("Mode: grounding-aware (expansion after grounding)")
    print()

    if args.legacy:
        _run_legacy_pipeline(
            theme, theme_doc, theme_doc_path, output_dir,
            model=args.model,
            skip_grounding=args.skip_grounding,
            use_cache=use_cache,
            check_signatures=args.check_signatures,
        )
    else:
        _run_grounded_pipeline(
            theme, theme_doc, theme_doc_path, output_dir,
            model=args.model,
            skip_grounding=args.skip_grounding,
            use_cache=use_cache,
            check_signatures=args.check_signatures,
        )


def _run_grounded_pipeline(
    theme: str,
    theme_doc: str | None,
    theme_doc_path: str | None,
    output_dir: Path,
    *,
    model: str,
    skip_grounding: bool,
    use_cache: bool,
    check_signatures: bool = False,
) -> None:
    """New pipeline: skeleton → grounding → grounded expansion → assembly.

    The expansion pass receives Mathlib source snippets from grounding and
    oracle exemplars from the repo, grounding the LLM's signatures in real
    Lean 4 API usage.
    """
    # Stage 1a: Skeleton pass.
    print("[1/4] Generating skeleton...")
    skeleton = skeleton_pass(
        theme, theme_doc, model=model, use_cache=use_cache,
    )
    n_defs = len(skeleton.get("definitions", []))
    n_lemmas = len(skeleton.get("lemmas", []))
    print(f"  Skeleton: {n_defs} definitions, {n_lemmas} lemmas")
    if skeleton.get("layers"):
        print(f"  Layers: {', '.join(skeleton['layers'])}")
    print()

    # Stage 1b: Skeleton grounding (to get source_text for expansion).
    skeleton_grounded = None
    if not skip_grounding:
        print("[2/4] Grounding skeleton against Mathlib (collecting source context)...")
        skeleton_grounded = ground_skeleton(skeleton, theme, use_cache=use_cache)
        snippets_total = sum(
            len(gd.grounding.source_snippets) for gd in skeleton_grounded.definitions
        ) + sum(
            len(gl.grounding.source_snippets) for gl in skeleton_grounded.lemmas
        )
        print(f"  Collected {snippets_total} Mathlib source snippets for expansion context")
    else:
        print("[2/4] Skipping skeleton grounding (--skip-grounding)")
    print()

    # Stage 2: Grounded expansion.
    print("[3/4] Expanding with grounding context + oracle exemplars...")
    decomposition = expand_with_grounding(
        theme, skeleton, theme_doc,
        grounded=skeleton_grounded,
        model=model,
        use_cache=use_cache,
    )
    print(f"  Produced {len(decomposition.definitions)} definitions, "
          f"{len(decomposition.lemmas)} lemmas")
    print()

    # Stage 3: Full grounding of expanded items.
    if not skip_grounding:
        print("[4/4] Re-grounding expanded decomposition...")
        grounded = ground(decomposition, use_cache=use_cache)
        novel = sum(
            1 for d in grounded.definitions if d.grounding.status == "novel"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "novel"
        )
        exists = sum(
            1 for d in grounded.definitions if d.grounding.status == "exists"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "exists"
        )
        partial = sum(
            1 for d in grounded.definitions if d.grounding.status == "partial_overlap"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "partial_overlap"
        )
        print(f"  Novel: {novel}, Exists: {exists}, Partial overlap: {partial}")
    else:
        print("[4/4] Skipping re-grounding (--skip-grounding)")
        from library_architect.models import (
            GroundedDecomposition,
            GroundedDefinition,
            GroundedLemma,
            GroundingResult,
        )
        ungrounded = GroundingResult(status="ungrounded", notes="Grounding skipped.")
        grounded = GroundedDecomposition(
            theme=theme,
            definitions=[
                GroundedDefinition(sketch=d, grounding=ungrounded)
                for d in decomposition.definitions
            ],
            lemmas=[
                GroundedLemma(sketch=l, grounding=ungrounded)
                for l in decomposition.lemmas
            ],
            layers=decomposition.layers,
        )
    print()

    # Stage 4: Assembly.
    print("Assembling blueprint...")
    blueprint = assemble(
        grounded,
        output_dir=output_dir,
        theme_doc_path=theme_doc_path,
    )
    _print_summary(blueprint, output_dir)

    # Optional: Elaboration check.
    if check_signatures:
        _run_elaboration_check(blueprint, output_dir)


def _run_legacy_pipeline(
    theme: str,
    theme_doc: str | None,
    theme_doc_path: str | None,
    output_dir: Path,
    *,
    model: str,
    skip_grounding: bool,
    use_cache: bool,
    check_signatures: bool = False,
) -> None:
    """Legacy pipeline: decompose (skeleton+expansion) → ground → assemble.

    Kept for backward compatibility. Does not inject grounding context or
    oracle exemplars into the expansion prompt.
    """
    # Stage 1: Decompose.
    print("[1/3] Decomposing theme...")
    decomposition = decompose(theme, theme_doc, model=model, use_cache=use_cache)
    print(f"  Produced {len(decomposition.definitions)} definitions, "
          f"{len(decomposition.lemmas)} lemmas")
    if decomposition.layers:
        print(f"  Layers: {', '.join(decomposition.layers)}")
    print()

    # Stage 2: Ground.
    if skip_grounding:
        print("[2/3] Skipping grounding (--skip-grounding).")
        from library_architect.models import (
            GroundedDecomposition,
            GroundedDefinition,
            GroundedLemma,
            GroundingResult,
        )
        ungrounded = GroundingResult(status="ungrounded", notes="Grounding skipped.")
        grounded = GroundedDecomposition(
            theme=theme,
            definitions=[
                GroundedDefinition(sketch=d, grounding=ungrounded)
                for d in decomposition.definitions
            ],
            lemmas=[
                GroundedLemma(sketch=l, grounding=ungrounded)
                for l in decomposition.lemmas
            ],
            layers=decomposition.layers,
        )
    else:
        print("[2/3] Grounding against Mathlib via LeanExplore...")
        from library_architect.grounder import ground
        grounded = ground(decomposition, use_cache=use_cache)
        novel = sum(
            1 for d in grounded.definitions if d.grounding.status == "novel"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "novel"
        )
        exists = sum(
            1 for d in grounded.definitions if d.grounding.status == "exists"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "exists"
        )
        partial = sum(
            1 for d in grounded.definitions if d.grounding.status == "partial_overlap"
        ) + sum(
            1 for l in grounded.lemmas if l.grounding.status == "partial_overlap"
        )
        print(f"  Novel: {novel}, Exists: {exists}, Partial overlap: {partial}")
    print()

    # Stage 3: Assemble.
    print("[3/3] Assembling blueprint...")
    blueprint = assemble(
        grounded,
        output_dir=output_dir,
        theme_doc_path=theme_doc_path,
    )
    _print_summary(blueprint, output_dir)

    # Optional: Elaboration check.
    if check_signatures:
        _run_elaboration_check(blueprint, output_dir)


def _run_elaboration_check(blueprint, output_dir: Path) -> None:
    """Run sorry-elaboration check on all planned blueprint entries."""
    from library_architect.elaboration_checker import check_blueprint

    print()
    print("Running signature elaboration check...")
    entries = [e.to_dict() for e in blueprint.entries]
    report = check_blueprint(entries)

    print()
    print(f"Elaboration check results:")
    print(f"  Total: {report.total}")
    print(f"  Passed: {report.passed}")
    print(f"  Failed: {report.failed}")
    print(f"  Skipped: {report.skipped}")

    if report.failed > 0:
        print()
        print("Failed signatures:")
        for r in report.results:
            if not r.passed:
                print(f"  {r.name}: {r.error_message.split(chr(10))[0][:100]}")

    # Write report to output directory.
    import json
    report_path = output_dir / "elaboration_report.json"
    report_path.write_text(
        json.dumps(report.to_dict(), indent=2),
        encoding="utf-8",
    )
    print()
    print(f"Elaboration report written to: {report_path}")


def _print_summary(blueprint, output_dir: Path) -> None:
    """Print final summary after assembly."""
    print(f"  Entries: {len(blueprint.entries)}")
    print(f"  Planned: {blueprint.summary.planned_count}")
    print(f"  Exists in Mathlib: {blueprint.summary.exists_count}")
    print()
    print(f"Blueprint written to:")
    print(f"  {output_dir / 'BLUEPRINT.md'}")
    print(f"  {output_dir / 'blueprint.json'}")
    if blueprint.summary.planned_count > 0:
        print(f"  {output_dir / 'lemma_specs/'} ({blueprint.summary.planned_count} specs)")
    print()
    print("Done. Review BLUEPRINT.md before proceeding to the Library Expander.")


if __name__ == "__main__":
    main()
