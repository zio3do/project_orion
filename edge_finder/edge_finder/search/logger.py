"""JSONL search log writer.

Appends one log entry per search query to a JSONL file. Each entry contains the
event type, timestamp, and full SearchResponse payload. This is the audit trail
that allows a human to inspect every query the edge finder ran and what it found.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
import json
from pathlib import Path
from typing import Any

from edge_finder.search.models import SearchResponse


@dataclass(frozen=True)
class SearchLogEntry:
    event: str
    created_at: str
    payload: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return {
            "event": self.event,
            "created_at": self.created_at,
            "payload": self.payload,
        }


def log_search_response(log_path: str | Path, response: SearchResponse) -> None:
    path = Path(log_path)
    path.parent.mkdir(parents=True, exist_ok=True)

    entry = SearchLogEntry(
        event="leanexplore.search",
        created_at=datetime.now().isoformat(),
        payload=response.to_dict(),
    )

    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry.to_dict(), ensure_ascii=True) + "\n")
