"""Module 4: Pocket Synthesis.

Sends density/gap evidence to the OpenAI API and receives a candidate mini-library
blueprint including proposed abstractions, candidate lemmas, dependency sketch,
justification, and risk level. NOTE: This module was implemented before per-concept
verification exists. Its output is not yet grounded in rigorous evidence. See
edge_finder_architecture.md section 3 (Module 4 assessment) for details.
"""

from __future__ import annotations

import json
from typing import Any

from edge_finder.llm.client import LlmClient
from edge_finder.prompts import build_pocket_synthesis_prompt


def synthesize_pocket(
    *,
    theme: str,
    evidence: dict[str, Any],
    model: str = "gpt-4o-mini",
) -> dict[str, Any]:
    client = LlmClient(model=model)
    prompt = build_pocket_synthesis_prompt(theme, evidence)
    raw = client.complete_json(prompt)
    return json.loads(raw)
