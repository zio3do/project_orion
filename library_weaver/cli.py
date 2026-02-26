"""
CLI entry point for Library Weaver.

Usage:
    python -m library_weaver <blueprint_dir> [--project-root <path>] [--dry-run]

The CLI is a thin wrapper around weaver.weave(). It parses arguments,
resolves paths, and prints progress. All orchestration logic lives in
weaver.py.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from library_weaver.weaver import weave


def main() -> None:
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        prog="library_weaver",
        description=(
            "Library Weaver — executes a blueprint end-to-end by invoking "
            "the Proof Oracle for each entry in dependency order."
        ),
    )

    parser.add_argument(
        "blueprint_dir",
        type=Path,
        help="Path to the Library Architect output directory "
             "(containing blueprint.json and lemma_specs/).",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=None,
        help="Lean project root directory (default: current working directory).",
    )
    parser.add_argument(
        "--run-dir",
        type=Path,
        default=None,
        help="Directory for run artifacts (default: library_weaver/runs/<run_id>/).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print execution plan without invoking the Proof Oracle.",
    )
    parser.add_argument(
        "--done",
        type=str,
        default=None,
        help="Comma-separated list of entry names to pre-mark as done "
             "(for resuming a previous run).",
    )

    args = parser.parse_args()

    # Validate blueprint_dir exists
    if not args.blueprint_dir.exists():
        print(f"Error: Blueprint directory not found: {args.blueprint_dir}",
              file=sys.stderr)
        sys.exit(1)

    # Parse --done into a frozenset
    done_entries: frozenset[str] | None = None
    if args.done:
        done_entries = frozenset(
            name.strip() for name in args.done.split(",") if name.strip()
        )

    print("Library Weaver v0.1.0")

    try:
        result = weave(
            blueprint_dir=args.blueprint_dir,
            project_root=args.project_root,
            run_dir=args.run_dir,
            dry_run=args.dry_run,
            done_entries=done_entries,
        )
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except ValueError as e:
        print(f"Validation error: {e}", file=sys.stderr)
        sys.exit(1)

    if not args.dry_run and result.failed_count > 0:
        sys.exit(2)  # Non-zero exit for failures
