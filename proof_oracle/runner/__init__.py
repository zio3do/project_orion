# proof_oracle.runner — Python orchestration layer
#
# Modules:
#   verifier.py      — Hard verification gate (lake env lean + sorry/axiom scan)
#   manifest.py      — MANIFEST.md reader/writer for tracking attempt history
#   prompt_builder.py — Constructs proof agent prompts from lemma specs
#   session.py       — Claude Code session manager (invoke, parse END_REASON)
#   orchestrator.py  — Top-level entry point: reads lemma spec, runs proof loop
