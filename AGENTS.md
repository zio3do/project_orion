# AGENTS.md

# AI Collaboration & Documentation Constitution

## Purpose

This repository is developed collaboratively between a human researcher and AI agents.

The primary risk is not incorrect code — it is **loss of conceptual clarity** due to high-volume AI code generation.

This document defines the documentation and architectural principles that all AI agents must follow when contributing to this repository.

---

# 1. Core Principle: Explainability Density > Code Volume

The goal of this project is not maximum code output.

The goal is:

- High conceptual clarity
- Controlled architectural growth
- Transferable ownership
- Inspectable reasoning
- Long-term maintainability

If a subsystem cannot be explained clearly, it is not ready to be implemented.

---

# 2. Documentation is a Deliverable, Not an Afterthought

Every non-trivial subsystem must produce documentation artifacts before and after implementation.

If a change introduces more than ~300 lines of code or a new conceptual abstraction, documentation is mandatory.

Required artifacts:

- Architecture overview
- Data flow explanation
- Mental model guide
- Critical invariants list
- Failure mode analysis
- Safe refactor guide

No subsystem should exist without a readable narrative explanation.

---

# 3. Docs-First Development Protocol

For any new subsystem, the agent must follow this sequence:

## Phase 1 — Design & Architecture (No Code Yet)

Generate a markdown document that includes:

1. Problem statement
2. Goals and non-goals
3. High-level architecture (component breakdown)
4. Data flow description
5. Sequence diagram (Mermaid if applicable)
6. Key design decisions
7. Alternatives considered
8. Known risks

Implementation may only proceed after this conceptual model is clear.

---

## Phase 2 — Implementation

When implementing:

- Files must begin with a high-level overview comment.
- No function longer than 40–60 lines without justification.
- Each module must state its responsibility in 3–5 sentences.
- Avoid unnecessary abstractions.
- Prefer vertical slices over broad scaffolding.

---

## Phase 3 — Ownership Transfer Document

After implementation, generate:

`SUBSYSTEM_NAME_WALKTHROUGH.md`

It must include:

1. What this subsystem does in one paragraph
2. The mental model for understanding it
3. Directory structure explained
4. Call graph explanation
5. Execution lifecycle walkthrough
6. Annotated excerpts of key functions
7. Critical invariants
8. Things that must not be broken
9. Most dangerous refactor mistakes
10. Open questions and technical debt

This document should be written as if onboarding a new engineer who will maintain the subsystem independently.

---

# 4. Lean / Mathlib-Specific Discipline

Because this repository interacts with Lean and Mathlib:

- Every abstraction must explain:
  - Which mathematical concept it models
  - Which Mathlib structures it depends on
  - What invariants are required for soundness
- If extending or wrapping Mathlib, explain:
  - Why existing tools are insufficient
  - What conceptual “pocket” is being filled
- Avoid opaque metaprogramming unless documented thoroughly.

Mathematical clarity is as important as software clarity.

---

# 5. Architectural Constraints

To prevent architectural drift:

- Before introducing a new directory, explain why it is necessary.
- Before introducing a new abstraction layer, justify its existence.
- Before introducing a new dependency, explain tradeoffs.
- Prefer composable modules over monolithic engines.
- Prefer explicit data flow over hidden global state.

If an architectural decision is non-trivial, generate an ADR (Architecture Decision Record).

---

# 6. Mental Model Artifacts (Mandatory for Complex Systems)

For complex subsystems, generate:

- Concept map
- Dependency graph
- State transition diagram (if applicable)
- “What would break if removed” analysis
- 3–5 core invariants
- Failure mode list

The purpose is to compress the cognitive load of the subsystem.

---

# 7. Incrementalism Over Ambition

The agent must:

- Implement the smallest possible vertical slice.
- Avoid speculative generality.
- Avoid building frameworks before concrete use cases.
- Avoid premature optimization.

Mini-libraries should grow from real proof needs, not hypothetical abstraction.

---

# 8. Anti-Patterns to Avoid

The agent must avoid:

- Over-engineered abstraction hierarchies
- Excessive metaprogramming without walkthrough docs
- Massive multi-file refactors without architectural explanation
- Generating code that cannot be summarized in <500 words
- “Magic” automation layers without transparent logic

If the subsystem cannot be explained simply, it is too complex.

---

# 9. Review Trigger Conditions

The agent must pause and request architectural review if:

- A subsystem crosses 1,000 lines
- A new core abstraction is introduced
- Lean metaprogramming becomes central
- The data model changes significantly
- A decision affects future mini-library extensibility

Major changes require a design doc update.

---

# 10. Definition of Done

A subsystem is considered complete only if:

- The code compiles
- The documentation exists
- The subsystem can be explained clearly
- Invariants are documented
- Failure modes are understood
- Another engineer could safely modify it

Clarity is part of correctness.

---

# 11. Philosophy of This Project

This repository is building an AI-assisted mathematical formalization engine.

The hardest problems are:

- Concept modeling
- Integration boundaries
- Mathematical abstraction alignment
- Long-term architectural coherence

The biggest risk is uncontrolled complexity growth.

Therefore:

> The AI must optimize for conceptual compression, not code production.

---

# 12. Meta Rule

If unsure whether to write more code or more explanation:

Write more explanation.