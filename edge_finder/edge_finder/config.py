"""Shared configuration constants and run metadata.

Defines the default output directory for run artifacts and the RunMetadata
dataclass used to stamp each run report with version and timestamp information.
"""

from dataclasses import dataclass
from datetime import datetime


DEFAULT_OUTPUT_DIR = "edge_finder/runs/edge_finder"


@dataclass(frozen=True)
class RunMetadata:
    version: str
    generated_at: str


def build_metadata(version: str) -> RunMetadata:
    return RunMetadata(version=version, generated_at=datetime.now().isoformat())
