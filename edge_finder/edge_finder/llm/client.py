"""OpenAI API client wrapper with retry and context-window management.

Wraps the OpenAI Responses API to provide JSON-mode completions with automatic
retry on rate limits (exponential backoff) and context length overflow (prompt
truncation at 50%). Estimates token counts using a character-based heuristic
rather than a tokenizer to avoid an additional dependency.
"""

from __future__ import annotations

import os
import time

from openai import OpenAI


# Approximate token limits for known models (input tokens).
# Conservative estimates to leave room for the response.
MODEL_INPUT_LIMITS: dict[str, int] = {
    "gpt-4o-mini": 110_000,
    "gpt-4o": 110_000,
    "gpt-4-turbo": 110_000,
    "gpt-3.5-turbo": 14_000,
}

DEFAULT_INPUT_LIMIT = 110_000

# Rough chars-per-token ratio for English/code text.
CHARS_PER_TOKEN_ESTIMATE = 3.5


def estimate_tokens(text: str) -> int:
    return int(len(text) / CHARS_PER_TOKEN_ESTIMATE)


class LlmClient:
    def __init__(self, api_key: str | None = None, model: str = "gpt-4o-mini"):
        key = api_key or os.getenv("OPENAI_API_KEY")
        if not key:
            raise ValueError("OPENAI_API_KEY is required")
        self._client = OpenAI(api_key=key)
        self._model = model
        self._max_input_tokens = MODEL_INPUT_LIMITS.get(model, DEFAULT_INPUT_LIMIT)

    def complete_json(self, prompt: str, *, max_retries: int = 3) -> str:
        prompt = self._truncate_if_needed(prompt)

        last_error: Exception | None = None
        for attempt in range(max_retries):
            try:
                response = self._client.responses.create(
                    model=self._model,
                    input=prompt,
                    text={"format": {"type": "json_object"}},
                )
                return response.output_text
            except Exception as exc:
                last_error = exc
                error_str = str(exc)
                # Context length exceeded — truncate more aggressively and retry
                if "context_length_exceeded" in error_str:
                    prompt = self._truncate_if_needed(prompt, factor=0.5)
                    continue
                # Rate limit — back off and retry
                if "429" in error_str or "rate_limit" in error_str.lower():
                    wait = 2**attempt
                    time.sleep(wait)
                    continue
                # Other errors — don't retry
                raise

        raise RuntimeError(
            f"LLM call failed after {max_retries} attempts: {last_error}"
        )

    def _truncate_if_needed(self, prompt: str, factor: float = 1.0) -> str:
        limit = int(self._max_input_tokens * factor)
        char_limit = int(limit * CHARS_PER_TOKEN_ESTIMATE)
        if len(prompt) <= char_limit:
            return prompt
        # Keep the beginning (instructions) and truncate the middle (data).
        # Find the last complete line within the limit.
        truncated = prompt[:char_limit]
        last_newline = truncated.rfind("\n")
        if last_newline > char_limit // 2:
            truncated = truncated[:last_newline]
        return truncated + "\n\n[... evidence truncated to fit context window ...]\n"
