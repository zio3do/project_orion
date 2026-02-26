"""
Shared configuration for the Library Architect module.

Defines output directory defaults, model settings, and run metadata.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone


DEFAULT_OUTPUT_DIR = "library_architect/runs"
DEFAULT_THEME_DIR = "library_architect/themes"

# LLM model for decomposition and assembly steps.
DECOMPOSER_MODEL = "gpt-4o"
ASSEMBLER_MODEL = "gpt-4o"

# LeanExplore settings for grounding.
GROUNDING_RESULTS_PER_QUERY = 10


@dataclass(frozen=True)
class RunMetadata:
    """Stamps each run with version and timestamp."""
    version: str
    generated_at: str


def build_metadata(version: str = "0.1.0") -> RunMetadata:
    return RunMetadata(
        version=version,
        generated_at=datetime.now(timezone.utc).isoformat(),
    )
