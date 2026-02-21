"""Module 1: Concept Generator (Hypothesis Layer).

Given a mathematical theme, calls the OpenAI API to produce a structured JSON
hypothesis of what primitives, operators, identity families, candidate namespaces,
and search queries should exist in Mathlib for that theme. This is the "what
should exist" step -- it generates hypotheses, not claims about Mathlib.
"""

from __future__ import annotations

import json
from typing import Any

from edge_finder.llm.client import LlmClient
from edge_finder.prompts import build_concept_generator_prompt


def generate_concepts(theme: str, *, model: str = "gpt-4o-mini") -> dict[str, Any]:
    client = LlmClient(model=model)
    prompt = build_concept_generator_prompt(theme)
    raw = client.complete_json(prompt)
    return json.loads(raw)
