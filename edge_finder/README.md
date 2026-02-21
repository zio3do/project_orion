# Edge Finder

Edge Finder is the first pillar of Project Orion. Given a mathematical theme
(e.g., "tropical geometry", "group homomorphisms"), it identifies the emptiest
gaps in Mathlib's coverage and ranks pocket candidates for future formalization.

The output is a ranked list of mathematical concepts that are absent or
under-represented in Mathlib, scored by feasibility, impact, and novelty --
entirely through algorithmic heuristics with no LLM involvement in scoring.

## Architecture

The pipeline has four modules that run sequentially:

```
Theme
  |
  v
[Module 1: Concept Generator]     LLM generates hypothesized concepts
  |                                and search queries for the theme
  v
[Module 2: Search + Verification]  LeanExplore semantic search + two-pass
  |                                verification against Mathlib declarations
  v
[Module 3: Density + Gap Analysis] Algorithmic density metrics and gap
  |                                classification from verification data
  v
[Module 4: Candidate Ranker]       Scores and clusters absent/partial concepts
  |                                into ranked pocket candidates
  v
candidates.json
```

Key design decisions:
- **LLM generates, algorithms judge.** The LLM proposes concepts; scoring uses
  only deterministic heuristics (verification status, namespace novelty, cluster
  density). This makes rankings reproducible and inspectable.
- **Two-pass verification.** Pass 1 runs broad theme-level search. Pass 2 runs
  targeted per-concept queries for under-covered concepts, reducing false
  absences.
- **Concept re-mapping (Iteration 5).** An LLM step grounds generated concept
  names to actual Mathlib declaration names observed in search results,
  addressing naming convention mismatches.

## Prerequisites

- Python 3.11+
- OpenAI API key (`OPENAI_API_KEY`)
- LeanExplore API key (`LEANEXPLORE_API_KEY`)

## Setup

```bash
# From repo root
python3 -m venv edge_finder/venv
source edge_finder/venv/bin/activate
pip install openai httpx
```

Create a `.env` file in the repo root:

```
OPENAI_API_KEY=...
LEANEXPLORE_API_KEY=...
```

## Usage

From the repo root:

```bash
PYTHONPATH=edge_finder edge_finder/venv/bin/python -m edge_finder \
  --theme "tropical geometry"
```

### Key CLI flags

| Flag | Default | Description |
|---|---|---|
| `--theme` | (required) | Mathematical theme to investigate |
| `--model` | `gpt-4o-mini` | OpenAI model for concept generation |
| `--search-limit` | `20` | Max results per LeanExplore query |
| `--dry-run` | off | Skip OpenAI calls; requires `--concepts-path` |
| `--skip-targeted-search` | off | Skip pass 2 targeted queries |
| `--skip-remap` | off | Skip LLM concept re-mapping |

### Dry-run mode

Dry-run skips all OpenAI calls and uses a cached concepts file. This is the
cheapest way to iterate on search, verification, and analysis logic:

```bash
PYTHONPATH=edge_finder edge_finder/venv/bin/python -m edge_finder \
  --theme "finite sums" \
  --dry-run \
  --concepts-path edge_finder/edge_finder/sample_concepts.json
```

## Output

Each run creates a timestamped directory under `edge_finder/runs/`:

| File | Description |
|---|---|
| `concepts.json` | LLM-generated concept hypothesis |
| `concepts_remapped.json` | Concepts grounded to Mathlib names |
| `verification.json` | Per-concept verification (status, match evidence) |
| `candidates.json` | Ranked pocket candidates with scores and justification |
| `search_responses.json` | Raw LeanExplore search results |
| `run_*.json` | Combined run report with all artifacts |

### Example: candidates.json

Each candidate cluster contains absent/partial concepts with a composite score:

```json
{
  "clusters": [
    {
      "label": "TropicalSemiring.toOrderedSemiring",
      "score": 0.85,
      "concepts": ["TropicalSemiring.toOrderedSemiring"],
      "feasibility": "Medium",
      "justification": "No existing declarations in namespace...",
      "risk": "Requires new algebraic structure definitions"
    }
  ]
}
```

Scores are deterministic: identical inputs always produce identical rankings.

## Design documentation

Detailed design docs are in `edge_finder/docs/`:

| Document | Contents |
|---|---|
| `edge_finder_architecture.md` | Full architecture, iteration history, design decisions |
| `edge_finder_walkthrough.md` | Codebase walkthrough and maintenance guide |
| `edge_finder_usage.md` | Detailed CLI reference and output format specs |
| `candidate_ranker/` | Module 4 design doc and ownership transfer walkthrough |
| `verification/` | Verification subsystem design doc and walkthrough |
