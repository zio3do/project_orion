# Examples — Cherry-Picked Run Artifacts

These files are representative outputs from Project Orion's first end-to-end run
on the **Graded Order Combinatorics** theme.

## Files

- **`BLUEPRINT.md`** — The decomposition blueprint produced by Library Architect (Pillar 3).
  Contains 2 definitions and 17 lemmas across 3 dependency layers, with full
  Lean 4 signatures, informal descriptions, proof hints, and a dependency graph.

- **`WEAVE_REPORT.md`** — The execution report from Library Weaver (Pillar 4).
  Shows the final DAG walk: 7/7 entries proved in a single automated run (1h 10m).

- **`proof_session_level_mem_iff/`** — A representative Proof Oracle session (Pillar 2).
  Contains the MANIFEST (run metadata) and raw session log for `level_mem_iff`,
  proved on the first attempt ($0.51, 5 LLM turns, ~13 min).
