"""
Library Architect — Pillar 3 of Project Orion.

Takes a mathematical theme and produces a blueprint: a dependency-ordered
plan of definitions and lemmas, each with a complete LemmaSpec ready for
the Proof Oracle (Pillar 2).

Three-component pipeline:
  Decomposer (LLM)  →  Grounder (LeanExplore)  →  Blueprint Assembler (algo)

Input:  theme name + optional theme document (markdown)
Output: BLUEPRINT.md (human-readable) + blueprint.json (machine-consumable)
"""
