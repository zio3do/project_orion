# Project Orion

An AI-assisted mathematical formalization engine for Lean 4. Given an underdeveloped area of Mathlib, it decomposes it into a structured library blueprint and proves every entry automatically — producing a complete, verified Lean 4 library with zero `sorry` and zero `axiom`.

## First End-to-End Result

Target: **Graded Order Combinatorics** (level sets, rank-generating polynomials, saturated chains over graded posets).

| Metric | Value |
|--------|-------|
| Definitions | 2 |
| Theorems proved | 16 |
| Lean 4 source | 250 lines, 3 files |
| `sorry` / `axiom` | 0 |
| Automated cost | ~$6.80 |
| Wall time (final weave) | 1h 10m |

The output compiles cleanly against Lean 4 v4.29.0-rc2 and Mathlib.

## Architecture

The system is organized into five pillars, each an independent Python module with its own CLI, data models, and documentation:

```
                    ┌─────────────────┐
                    │  1. Edge Finder  │   Identifies underdeveloped Mathlib pockets
                    └────────┬────────┘
                             │ theme
                             ▼
                    ┌─────────────────────┐
                    │  3. Library Architect│   Decomposes theme → dependency-ordered blueprint
                    └────────┬────────────┘
                             │ blueprint (DAG of lemma specs)
                             ▼
                    ┌─────────────────────┐
                    │  4. Library Weaver   │   Walks DAG, accumulates .lean files
                    └────────┬────────────┘
                             │ invokes per entry
                             ▼
                    ┌─────────────────────┐
                    │  2. Proof Oracle     │   Proves one lemma via Claude Code + MCP
                    └────────┬────────────┘
                             │ verified .lean proof
                             ▼
                    ┌─────────────────────┐
                    │  5. Proof Foundry    │   (future) Assembles into Mathlib PRs
                    └─────────────────────┘
```

### Pillar 1: Edge Finder

Identifies underdeveloped "pockets" in Mathlib by combining LLM concept generation, LeanExplore search, and algorithmic scoring. Outputs ranked theme candidates with coverage gaps.

- Design: [`edge_finder/docs/edge_finder_architecture.md`](edge_finder/docs/edge_finder_architecture.md)
- Walkthrough: [`edge_finder/docs/edge_finder_walkthrough.md`](edge_finder/docs/edge_finder_walkthrough.md)

### Pillar 2: Proof Oracle

Proves individual lemmas by spawning fresh Claude Code sessions equipped with `lean-lsp-mcp` (compiler diagnostics) and `LeanExplore` (Mathlib search) via MCP. Each proof attempt is hard-gated: `lake env lean` must report zero errors, zero `sorry`, zero `axiom`, and the target lemma name must be present in the file.

- Design: [`proof_oracle/docs/proof_oracle_design.md`](proof_oracle/docs/proof_oracle_design.md)
- Walkthrough: [`proof_oracle/docs/proof_oracle_walkthrough.md`](proof_oracle/docs/proof_oracle_walkthrough.md)

### Pillar 3: Library Architect

Decomposes a mathematical theme into a dependency-ordered blueprint of definitions and lemmas. Uses a two-pass pipeline: (1) skeleton pass for mathematical intent, (2) grounded expansion pass using LeanExplore to anchor every signature against real Mathlib declarations. Each signature is individually verified via `lake env lean` elaboration.

- Design: [`library_architect/docs/library_architect_design.md`](library_architect/docs/library_architect_design.md)
- Walkthrough: [`library_architect/docs/LIBRARY_ARCHITECT_WALKTHROUGH.md`](library_architect/docs/LIBRARY_ARCHITECT_WALKTHROUGH.md)

### Pillar 4: Library Weaver

Executes a blueprint end-to-end. Walks the dependency DAG in topological order, accumulates Lean source files across entries, and invokes the Proof Oracle for each entry. Produces a weave report summarizing results, costs, and timings.

- Design: [`library_weaver/docs/library_weaver_design.md`](library_weaver/docs/library_weaver_design.md)
- Walkthrough: [`library_weaver/docs/LIBRARY_WEAVER_WALKTHROUGH.md`](library_weaver/docs/LIBRARY_WEAVER_WALKTHROUGH.md)

### Pillar 5: Proof Foundry (Future)

Assembles verified proofs into Mathlib-conformant pull requests. Not yet implemented.

## Output: Verified Lean 4 Library

The pipeline produced three verified Lean 4 files:

- [`Orion/GradedOrderCombinatorics/LevelSets.lean`](Orion/GradedOrderCombinatorics/LevelSets.lean) — Level set definition and partition properties
- [`Orion/GradedOrderCombinatorics/RankGenPoly.lean`](Orion/GradedOrderCombinatorics/RankGenPoly.lean) — Rank-generating polynomial and coefficient/evaluation theorems
- [`Orion/GradedOrderCombinatorics/SaturatedChains.lean`](Orion/GradedOrderCombinatorics/SaturatedChains.lean) — Saturated chain length, existence, uniqueness, strict monotonicity, and nodup

All theorems are machine-proved with no human proof assistance. See [`examples/`](examples/) for representative pipeline artifacts (blueprint, weave report, proof session log).

## Setup

### Prerequisites

- **Python 3.12+**
- **Lean 4** via [elan](https://github.com/leanprover/elan) (the `lean-toolchain` file pins the version)
- **Claude Code CLI** (`npm install -g @anthropic-ai/claude-code`)
- API keys for Claude, OpenAI, and LeanExplore

### Installation

```bash
# Clone and enter the repository
git clone https://github.com/<your-username>/project_orion.git
cd project_orion

# Set up Python environment
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

# Set up Lean (downloads toolchain + Mathlib on first build)
lake build

# Configure API keys
cp .env.example .env
# Edit .env with your CLAUDE_API_KEY, OPENAI_API_KEY, LEANEXPLORE_API_KEY
```

### Running the Pillars

Each pillar is a Python module with its own CLI:

```bash
# Edge Finder — discover underdeveloped Mathlib pockets
python -m edge_finder

# Library Architect — decompose a theme into a blueprint
python -m library_architect "Graded Order Combinatorics"

# Library Weaver — execute a blueprint end-to-end
python -m library_weaver library_architect/runs/graded_order_combinatorics/

# Proof Oracle — prove a single lemma (typically invoked by Weaver)
python -m proof_oracle proof_oracle/specs/some_lemma.json
```

## Repository Structure

```
project_orion/
├── Orion/                          # Verified Lean 4 source (pipeline output)
│   └── GradedOrderCombinatorics/   # 3 files, 250 lines, 2 defs + 16 theorems
├── edge_finder/                    # Pillar 1: Mathlib pocket discovery
│   ├── docs/                       # Architecture, design, walkthrough
│   ├── llm/                        # LLM client abstraction
│   └── ...
├── proof_oracle/                   # Pillar 2: Single-lemma proving
│   ├── docs/                       # Design doc, walkthrough
│   ├── runner/                     # Orchestrator, verifier, session manager
│   └── ...
├── library_architect/              # Pillar 3: Theme → blueprint decomposition
│   ├── docs/                       # Design doc, walkthrough
│   └── ...
├── library_weaver/                 # Pillar 4: Blueprint → verified library
│   ├── docs/                       # Design doc, walkthrough
│   └── ...
├── examples/                       # Cherry-picked run artifacts for reference
│   ├── BLUEPRINT.md                # Graded Order Combinatorics blueprint
│   ├── WEAVE_REPORT.md             # Final weave execution report
│   └── proof_session_level_mem_iff/# Representative proof session
├── docs/
│   └── PROJECT_RETROSPECTIVE.md    # Full project retrospective
├── ProjectOrion.lean               # Lean library root
├── lakefile.toml                   # Lake build configuration
├── lean-toolchain                  # Lean 4 version pin
├── requirements.txt                # Python dependencies
└── AGENTS.md                       # AI collaboration protocol
```

## Key Design Decisions

1. **Hard verification gate.** Every proof is verified by `lake env lean` — the actual Lean compiler, not an LLM self-report. The verifier checks zero errors, zero `sorry`, zero `axiom`, and confirms the target lemma name is present in the file.

2. **Grounded signatures.** Library Architect uses LeanExplore to search real Mathlib declarations before generating Lean 4 signatures. This eliminates hallucinated API names — the #1 failure mode in LLM-generated formal math.

3. **Frozen dataclass architecture.** All modules use frozen dataclasses with `to_dict()`/`from_dict()` for serialization. No shared code between modules. Each pillar is independently testable.

4. **Run-level artifact directories.** Every invocation of every pillar writes to a timestamped run directory containing all inputs, outputs, and logs. Runs are gitignored; representative examples are cherry-picked into `examples/`.

5. **Docs-first development.** Every subsystem has a design document (written before implementation) and a walkthrough document (written after). See [`AGENTS.md`](AGENTS.md) for the full protocol.

## Tech Stack

- **Lean 4** v4.29.0-rc2 + **Mathlib** — target proof language and library
- **Python 3.12** — orchestration, LLM interaction, pipeline control
- **Claude Code CLI** — proof agent runtime (spawns fresh sessions per lemma)
- **LeanExplore** — Mathlib declaration search (used in grounding + proof search)
- **lean-lsp-mcp** — Lean compiler diagnostics via MCP (used by proof agents)
- **OpenAI API** — decomposition and concept generation (Library Architect, Edge Finder)

## Further Reading

- [Project Retrospective](docs/PROJECT_RETROSPECTIVE.md) — challenges, lessons learned, and what worked
- [Example Blueprint](examples/BLUEPRINT.md) — the full Graded Order Combinatorics blueprint
- [Example Weave Report](examples/WEAVE_REPORT.md) — execution report from the final pipeline run
