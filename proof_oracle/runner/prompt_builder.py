"""
prompt_builder.py — Constructs proof agent prompts for Claude Code sessions.

Responsibility: Take a lemma specification, optional pre-searched Mathlib context,
and optional previous error history, and produce a complete prompt string that
gets passed to `claude -p`.

The prompt is the most critical design artifact. It must:
  1. State the lemma to prove clearly.
  2. Provide relevant Mathlib context.
  3. Instruct the agent on tool usage and proof search strategy.
  4. Enforce the sorry-not-axiom policy.
  5. Require the END_REASON sentinel on exit.

This module loads templates from proof_oracle/prompts/ and fills in per-lemma
details. The templates are plain text/markdown — no Jinja or other engine.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass
class LemmaSpec:
    """
    A single lemma specification — the input contract for the Proof Oracle.

    This mirrors the JSON schema defined in Section 5.2 of the design doc.
    """

    lemma_name: str
    target_file: str
    target_namespace: str
    informal_statement: str
    suggested_signature: str
    depends_on: list[str]
    hints: str = ""
    attempt_budget: int = 10
    difficulty: str = "easy"

    @classmethod
    def from_dict(cls, data: dict) -> LemmaSpec:
        """Create a LemmaSpec from a parsed JSON dict."""
        return cls(
            lemma_name=data["lemma_name"],
            target_file=data["target_file"],
            target_namespace=data.get("target_namespace", ""),
            informal_statement=data["informal_statement"],
            suggested_signature=data["suggested_signature"],
            depends_on=data.get("depends_on", []),
            hints=data.get("hints", ""),
            attempt_budget=data.get("attempt_budget", 10),
            difficulty=data.get("difficulty", "easy"),
        )


def _load_template(prompts_dir: Path, filename: str) -> str:
    """Load a prompt template file. Returns empty string if not found."""
    template_path = prompts_dir / filename
    if template_path.exists():
        return template_path.read_text(encoding="utf-8")
    return ""


def build_prompt(
    spec: LemmaSpec,
    prompts_dir: Path,
    project_root: Path,
    pre_search_context: str = "",
    previous_errors: str = "",
    attempt_number: int = 1,
) -> str:
    """
    Build the complete proof agent prompt.

    Args:
        spec: The lemma specification to prove.
        prompts_dir: Path to proof_oracle/prompts/ (contains templates).
        project_root: Path to the Lean project root.
        pre_search_context: Pre-fetched Mathlib context from LeanExplore.
        previous_errors: Error output from a previous failed attempt (for retries).
        attempt_number: Which attempt this is (1-indexed).

    Returns:
        Complete prompt string to pass to `claude -p`.
    """
    # Load the system prompt template
    system_prompt = _load_template(prompts_dir, "system_prompt.md")
    task_template = _load_template(prompts_dir, "task_template.md")

    # Build the task-specific section
    sections = []

    # -- Task header
    sections.append(f"# Task: Prove `{spec.lemma_name}`")
    sections.append("")

    # -- Attempt info
    if attempt_number > 1:
        sections.append(
            f"**This is attempt {attempt_number} of {spec.attempt_budget}.**"
        )
        sections.append("")

    # -- Lemma details
    sections.append("## Lemma Specification")
    sections.append("")
    sections.append(f"**Name:** `{spec.lemma_name}`")
    sections.append(f"**Informal statement:** {spec.informal_statement}")
    sections.append(f"**Target file:** `{spec.target_file}`")
    if spec.target_namespace:
        sections.append(f"**Namespace:** `{spec.target_namespace}`")
    sections.append("")
    sections.append("**Suggested Lean 4 signature:**")
    sections.append(f"```lean")
    sections.append(spec.suggested_signature)
    sections.append("```")
    sections.append("")

    # -- Dependencies
    if spec.depends_on:
        sections.append("## Dependencies")
        sections.append("")
        sections.append(
            "This lemma depends on the following definitions/lemmas "
            "(they should already exist in the target file):"
        )
        for dep in spec.depends_on:
            sections.append(f"- `{dep}`")
        sections.append("")

    # -- Hints
    if spec.hints:
        sections.append("## Proof Hints")
        sections.append("")
        sections.append(spec.hints)
        sections.append("")

    # -- Pre-searched Mathlib context
    if pre_search_context:
        sections.append("## Relevant Mathlib Context (Pre-Searched)")
        sections.append("")
        sections.append(
            "The following Mathlib declarations may be relevant to this proof. "
            "You can also search for more using the LeanExplore tool."
        )
        sections.append("")
        sections.append(pre_search_context)
        sections.append("")

    # -- Previous errors (retry context)
    if previous_errors:
        sections.append("## Previous Attempt Errors")
        sections.append("")
        sections.append(
            "Your previous attempt failed verification. Here are the errors. "
            "Please fix these issues in your new attempt:"
        )
        sections.append("")
        sections.append("```")
        sections.append(previous_errors.strip())
        sections.append("```")
        sections.append("")

    # -- Project info
    sections.append("## Project Information")
    sections.append("")
    sections.append(f"- **Project root:** `{project_root}`")
    sections.append(f"- **Lean version:** See `lean-toolchain` in project root")
    sections.append(f"- **Mathlib:** Available via `import Mathlib`")
    sections.append("")

    task_section = "\n".join(sections)

    # Assemble the final prompt: system prompt + task template + task specifics
    parts = []
    if system_prompt:
        parts.append(system_prompt.strip())
        parts.append("")
        parts.append("---")
        parts.append("")
    if task_template:
        parts.append(task_template.strip())
        parts.append("")
        parts.append("---")
        parts.append("")
    parts.append(task_section)

    return "\n".join(parts)
