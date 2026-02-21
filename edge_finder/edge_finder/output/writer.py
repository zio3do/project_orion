"""Run report serializer.

Writes the complete run report (theme, metadata, search responses, verification
report, density report, gap report) as a JSON file to the run output directory.
This is the final artifact of each edge finder run, intended for human review
and cross-run comparison.
"""

from __future__ import annotations

from dataclasses import asdict
from datetime import datetime
import json
from pathlib import Path
from typing import Any

from edge_finder.analysis.density import DensityReport
from edge_finder.analysis.heuristics import GapReport
from edge_finder.config import RunMetadata
from edge_finder.search.models import SearchResponse


def _slugify(text: str) -> str:
    return "".join(char.lower() if char.isalnum() else "_" for char in text).strip("_")


def write_run_report(
    *,
    theme: str,
    responses: list[SearchResponse],
    verification_report: Any,
    density_report: DensityReport,
    gap_report: GapReport,
    output_dir: Path,
    metadata: RunMetadata,
) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    slug = _slugify(theme)
    timestamp = datetime.now().strftime("%Y-%m-%d")
    output_path = output_dir / f"run_{timestamp}_{slug}.json"

    payload = {
        "theme": theme,
        "metadata": asdict(metadata),
        "responses": [response.to_dict() for response in responses],
        "verification_report": verification_report.to_dict(),
        "density_report": density_report.to_dict(),
        "gap_report": gap_report.to_dict(),
    }

    with output_path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, ensure_ascii=True, indent=2)

    return output_path
