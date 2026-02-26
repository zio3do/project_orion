"""proof_oracle — Pillar 2 of Project Orion.

Takes a single lemma specification and produces a verified Lean 4 proof.
Contract: one lemma spec in, one verified .lean proof out.

Architecture: Python orchestrator (this package) spawns Claude Code sessions
that use lean-lsp-mcp and LeanExplore MCP to write and verify proofs.
"""
