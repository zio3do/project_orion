# Edge Finder -- Module 4: Pocket Candidate Ranking

## Phase 1 Design Document

---

## 1. Problem Statement

The Edge Finder pipeline currently ends at gap classification (Module 3), which produces a `GapReport` containing:

- A `concept_coverage_gap` finding with a list of absent/partial concept names, a coverage ratio, and a confidence tier.
- A `density_context` finding with aggregate structural metrics.
- Optionally, a `well_covered` or `insufficient_signal` finding.

This output tells you *that* gaps exist, but not *which gaps are worth pursuing*. Not all absent concepts are equally promising as pocket candidates:

- Some absent concepts may be genuinely missing from Mathlib and represent real contribution opportunities (e.g., `TropicalVariety` -- a core abstraction with no formalization).
- Others may be absent because they are too specialized, too vague, or redundant with existing infrastructure (e.g., `TropicalPoint.transformation` -- a vague concept that doesn't correspond to a crisp mathematical definition).
- Some may cluster together into a coherent pocket (e.g., `TropicalVariety`, `TropicalIdeal`, `TropicalCurve` form a natural "tropical algebraic geometry" pocket), while others are isolated.

The new Module 4 must take the gap evidence and produce a **ranked list of pocket candidates** -- clusters of related absent/partial concepts that together represent a coherent, feasible mini-library contribution.

---

## 2. Goals and Non-Goals

### Goals

- **Cluster related absent/partial concepts** into coherent pocket candidates. A pocket is not a single missing lemma; it is a group of related concepts that together would form a useful mini-library.
- **Rank pocket candidates** by a composite score reflecting feasibility, coherence, and value.
- **Produce human-readable justification** for each candidate, explaining why it is promising and what makes it a coherent pocket.
- **Consume only existing pipeline data.** No new API calls (neither LLM nor LeanExplore). The module operates purely on the outputs of Modules 1-3.
- **Keep the output inspectable.** Each candidate must show which concepts it groups, what evidence supports it, and how the score was computed.

### Non-Goals

- **Blueprint generation.** This module does not propose what to build (no lemma lists, no dependency DAGs, no API designs). That belongs in a separate downstream subsystem.
- **LLM-based reasoning.** The ranking should be algorithmic and deterministic. Using an LLM to "judge" pocket quality reintroduces the same ungrounded-confidence problem that Module 4 (Pocket Synthesis) had.
- **Definitive recommendations.** The output is a ranked list of *candidates* for human review, not an instruction to build something. The human makes the final call.
- **Cross-theme analysis.** Each run produces candidates for a single theme. Comparing across themes is out of scope.

---

## 3. Inputs

Module 4 consumes the following pipeline artifacts, all produced by Modules 1-3:

| Input | Source | What it provides |
|---|---|---|
| `concepts` dict | Module 1 (Concept Generator) | Original concept structure: `primitives`, `operators`, `identity_families`, `candidate_namespaces`, `search_queries` |
| `VerificationReport` | Module 2 (Verification Layer) | Per-concept status (`verified`/`partial`/`absent`/`name_mismatch`), match evidence, searched queries |
| `DensityReport` | Module 3a (Density Analyzer) | Namespace distribution, module list, operator hits |
| `GapReport` | Module 3b (Gap Heuristics) | Gap findings with category, confidence, evidence |
| `SearchResponse[]` | Search layer | All search responses (theme + targeted). Provides the raw declaration names and modules for infrastructure assessment |

---

## 4. Output: `candidates.json`

```json
{
  "theme": "tropical geometry",
  "total_absent": 16,
  "total_partial": 0,
  "candidates": [
    {
      "rank": 1,
      "name": "Tropical Algebraic Geometry Core",
      "concepts": ["TropicalVariety", "TropicalIdeal", "TropicalCurve"],
      "concept_kinds": ["primitive", "primitive", "primitive"],
      "related_verified": ["Tropical", "Tropical.trop", "Tropical.trop_add"],
      "score": 0.82,
      "score_breakdown": {
        "cluster_size": 0.3,
        "infrastructure_proximity": 0.25,
        "concept_coherence": 0.27
      },
      "justification": [
        "3 absent primitives sharing the 'Tropical' namespace prefix",
        "Strong existing infrastructure: 60+ declarations in Tropical.* namespace",
        "Concepts are structurally related: variety, ideal, curve form a standard algebraic geometry triple",
        "All three are core mathematical objects with well-defined formalizations in the literature"
      ],
      "feasibility_notes": [
        "Tropical namespace already has semiring, lattice, and order infrastructure",
        "Would require defining TropicalVariety over a tropical semiring"
      ],
      "risk": "moderate"
    }
  ],
  "unclustered_concepts": ["TropicalPoint.transformation", "Tropical.max_eq_add"],
  "metadata": {
    "gap_confidence": "moderate",
    "coverage_ratio": 0.3043,
    "scoring_version": "1.0"
  }
}
```

---

## 5. High-Level Architecture

```
                    +------------------+
                    | Module 4:        |
                    | Pocket Candidate |
                    | Ranking          |
                    +--------+---------+
                             |
          +------------------+------------------+
          |                  |                  |
   +------v------+   +------v------+   +------v------+
   | Step 1:     |   | Step 2:     |   | Step 3:     |
   | Extract     |   | Cluster     |   | Score &     |
   | Under-      |   | Concepts    |   | Rank        |
   | covered     |   |             |   | Candidates  |
   +------+------+   +------+------+   +------+------+
          |                  |                  |
          v                  v                  v
   absent/partial     concept clusters     CandidateReport
   concept list       (grouped by          (ranked, with
   with metadata      namespace/kind)      justification)
```

### Step 1: Extract Under-Covered Concepts

From the `VerificationReport`, extract all concepts classified as `absent` or `partial`. For each, record:
- The concept name
- Its `ConceptKind` (primitive, operator, identity_family)
- Its verification status (absent vs. partial)
- The namespace prefix (first dot-separated segment, or the full name if no dots)
- Whether any verified concepts share the same namespace prefix (infrastructure proximity signal)

### Step 2: Cluster Concepts

Group under-covered concepts into candidate pockets using deterministic rules:

1. **Namespace prefix clustering.** Concepts sharing the same top-level namespace prefix are grouped together (e.g., `TropicalVariety`, `TropicalIdeal`, `TropicalCurve` all start with `Tropical`).

2. **Kind-based sub-clustering.** Within a namespace group, if the group is large (>5 concepts), split by `ConceptKind`: primitives form the core of a pocket, operators and identity families are supporting evidence.

3. **Singleton handling.** Concepts that don't cluster with any other concept are collected into an `unclustered_concepts` list. They are not discarded but are not promoted to pocket candidates.

4. **Minimum cluster size.** A cluster must contain at least 2 concepts to be a pocket candidate. A single missing concept is not a pocket; it is a specific gap.

### Step 3: Score and Rank

Each cluster is scored on three dimensions, each normalized to [0, 1]:

#### 3a. Cluster Size Score (weight: 0.3)

Larger clusters with more absent concepts suggest a more novel, substantial pocket. `absent` and `partial` concepts are counted separately because they differ in Mathlib novelty: an absent concept is fully unformalized, while a partial concept already has some coverage.

```
# absent concepts count fully; partial concepts count at half weight
effective_size = count(absent) + 0.5 * count(partial)
cluster_size_score = min(effective_size / 5, 1.0)
```

Rationale: All else equal, a cluster of 3 absent concepts ranks higher than a cluster of 3 partial concepts, because absent concepts represent a more genuine contribution opportunity. The 0.5 weight for partial is not a penalty — partial concepts still contribute positively to the score — but they contribute less because they indicate Mathlib already has some foothold in that area. The normalization target of 5 is the effective-size equivalent of 5 fully absent concepts.

#### 3b. Infrastructure Proximity Score (weight: 0.35)

Pockets near existing Mathlib infrastructure are more feasible because they can build on existing definitions and instances.

```
# Count verified concepts sharing the same namespace prefix as the cluster
related_verified = [v for v in verified_concepts if shares_prefix(v, cluster)]
infra_score = min(len(related_verified) / 3, 1.0)
```

Rationale: If Mathlib already has 3+ verified declarations in the same namespace, the infrastructure is strong. A pocket in `Tropical.*` where `Tropical`, `Tropical.trop`, `Tropical.trop_add` etc. already exist is much more feasible than a pocket in a namespace with zero existing declarations.

#### 3c. Concept Coherence Score (weight: 0.35)

Measures how tightly related the concepts within a cluster are.

```
# 1. All-primitives bonus: clusters of core types are more coherent than
#    clusters mixing types and lemmas
primitive_ratio = count(primitives) / len(concepts)

# 2. Name similarity: average pairwise longest common prefix length
#    among concept names (normalized by average name length)
name_similarity = avg_pairwise_lcp(concept_names) / avg_name_length

coherence_score = 0.5 * primitive_ratio + 0.5 * name_similarity
```

Rationale: A pocket where all concepts are primitives (core mathematical types) is more likely to form a coherent mini-library than a loose collection of identity families. Name similarity captures structural relatedness (e.g., `Matroid.intersection`, `Matroid.product`, `Matroid.circuit_completion` are clearly related).

#### Composite Score

```
score = 0.30 * cluster_size + 0.35 * infra_proximity + 0.35 * coherence
```

#### Risk Assessment

```
if gap_confidence == "high" and infra_proximity < 0.3:
    risk = "high"     # Big gap, little infrastructure to build on
elif gap_confidence == "high" and infra_proximity >= 0.3:
    risk = "moderate"  # Big gap, but infrastructure exists
elif gap_confidence in ("moderate", "low"):
    risk = "moderate"  # Smaller gap or uncertain signal
```

---

## 6. Key Design Decisions

| Decision | Rationale | Tradeoff |
|---|---|---|
| Purely algorithmic, no LLM | Deterministic, inspectable, reproducible. Avoids the "confident nonsense" problem of the old Module 4. | Cannot capture nuanced mathematical judgment about which pockets are intellectually interesting. |
| Namespace-prefix clustering | Simple, fast, and aligns with Mathlib's organizational structure. | May miss semantically related concepts across different namespaces. |
| Three-factor scoring | Balances size (substance), infrastructure (feasibility), and coherence (quality). | Weights are not empirically calibrated; they are reasonable defaults. |
| Minimum cluster size of 2 | A single missing concept is a gap, not a pocket. | Some genuinely important single-concept gaps will be relegated to `unclustered_concepts`. |
| No new API calls | Module 4 operates on existing data. Keeps cost at zero and latency at near-zero. | Cannot enrich candidates with additional search evidence. |
| Partial concepts weighted at 0.5 in cluster size score | `absent` concepts represent a genuine Mathlib novelty opportunity; `partial` concepts already have some Mathlib coverage. All else equal, a cluster of absent concepts should rank higher than a cluster of partial concepts. | The 0.5 weight is a reasonable default, not empirically calibrated. May need tuning if calibration shows partial concepts systematically under- or over-ranked. |

---

## 7. Alternatives Considered

1. **LLM-based pocket assessment.** Ask the LLM to judge which clusters are most promising. Rejected: this is exactly what the old Module 4 did, and it produced ungrounded output. The whole point of the redesign is to make Module 4 algorithmic.

2. **Cross-theme comparison.** Run the pipeline on multiple themes and compare candidates. Rejected as out of scope for this module. Could be a separate analysis tool that consumes multiple `candidates.json` files.

3. **Dependency-based clustering.** Use declaration dependencies from search results to cluster concepts. Rejected: search results include limited dependency information and it would require additional API calls to get full dependency graphs.

4. **Singleton promotion.** Allow single-concept candidates if the concept is a primitive type. Considered but deferred: the current minimum-2 rule is simpler and we can revisit if calibration shows important singletons being missed.

---

## 8. Known Risks

### R1: Namespace prefix is a weak clustering signal

Two concepts may share a namespace prefix but be unrelated (e.g., `Matroid.intersection` and `Matroid.dual_properties` are both Matroid concepts but target different aspects). Conversely, related concepts may have different prefixes (e.g., `IndepMatroid` and `Matroid.IsCircuit`).

**Mitigation:** The coherence score partially addresses this by rewarding name similarity. We accept this as a known limitation of a purely algorithmic approach.

### R2: Scoring weights are not empirically calibrated

The 0.30/0.35/0.35 split is a reasonable default but not grounded in data.

**Mitigation:** The score breakdown is always reported, so a human can override the ranking. Future calibration runs can tune these weights.

### R3: Concept generation quality limits candidate quality

If Module 1 generates poor concepts (too vague, too narrow, wrong names), the candidates will reflect that. Module 4 cannot fix upstream quality.

**Mitigation:** None at this layer. Upstream improvements (better prompts, better re-mapping) are the path forward.

### R4: Fixed-cluster approach may not capture "opportunity pockets"

The best pocket candidates may not be clusters of absent concepts but rather "holes" between verified concepts (e.g., a verified type with no verified operators). This module currently clusters absences, not holes.

**Mitigation:** Deferred. A "hole analysis" mode could be added later that examines the structure of verified concepts to find missing operators/lemmas.

---

## 9. Implementation Plan

### File: `edge_finder/edge_finder/analysis/candidates.py`

Estimated size: ~150-200 lines.

Key functions:
- `extract_under_covered(report: VerificationReport) -> list[UnderCoveredConcept]`
- `cluster_concepts(concepts: list[UnderCoveredConcept]) -> list[ConceptCluster]`
- `score_cluster(cluster: ConceptCluster, verified: list[str], gap_confidence: str) -> ScoredCandidate`
- `rank_candidates(verification: VerificationReport, density: DensityReport, gap: GapReport, concepts: dict, responses: list[SearchResponse]) -> CandidateReport`

### Data types (frozen dataclasses):

```python
@dataclass(frozen=True)
class UnderCoveredConcept:
    name: str
    kind: ConceptKind
    status: VerificationStatus  # absent or partial
    namespace_prefix: str

@dataclass(frozen=True)
class ScoredCandidate:
    rank: int
    name: str
    concepts: list[str]
    concept_kinds: list[str]
    related_verified: list[str]
    score: float
    score_breakdown: dict[str, float]
    justification: list[str]
    feasibility_notes: list[str]
    risk: str

@dataclass(frozen=True)
class CandidateReport:
    theme: str
    total_absent: int
    total_partial: int
    candidates: list[ScoredCandidate]
    unclustered_concepts: list[str]
    metadata: dict[str, object]
```

### Pipeline integration in `cli.py`:

```python
# After gap classification:
candidate_report = rank_candidates(
    verification=verification_report,
    density=density_report,
    gap=gap_report,
    concepts=concepts_for_verification,
    responses=all_responses,
    theme=args.theme,
)
# Write candidates.json
candidates_path = run_dir / "candidates.json"
with candidates_path.open("w") as f:
    json.dump(candidate_report.to_dict(), f, indent=2)
```

---

## 10. Success Criteria

The module is successful if, for the 6 calibration themes:

1. **Well-covered themes** (natural number addition, group homomorphisms) produce 0 or very few candidates with low scores.
2. **Sparse themes** (tropical geometry, combinatorial species) produce meaningful candidates that a mathematician would agree are promising pockets.
3. **Intermediate themes** (list operations, matroid theory) produce candidates that reflect the partial coverage -- some promising pockets where coverage is weakest.
4. **Rankings are stable** across re-runs of the same theme with cached concepts (deterministic output).
5. **The output is inspectable** -- a human reading `candidates.json` can understand why each candidate was ranked where it is.

### Calibration Results (Session 10)

**Overall verdict: PASS** (4 pass, 1 soft-pass).

| Theme | Coverage | Gap Conf | # Candidates | Top Score | Unclustered | Category |
|---|---|---|---|---|---|---|
| natural_number_addition | 0.61 | low | 3 | 0.74 | 2 | well-covered |
| group_homomorphisms | 0.67 | low | 3 | 0.61 | 2 | well-covered |
| list_operations | 0.57 | low | 2 | 0.73 | 3 | intermediate |
| matroid_theory | 0.33 | moderate | 2 | 0.61 | 5 | intermediate |
| tropical_geometry | 0.19 | high | 3 | 0.92 | 0 | sparse |
| combinatorial_species | 0.17 | high | 2 | 0.39 | 6 | sparse |

**Criterion 1 (well-covered → low scores): SOFT PASS.** Both themes produce candidates with moderate scores (0.61-0.74), not 0. Gap confidence is correctly "low" for both. The candidates exist because dry-run tests skip re-mapping, leaving more concepts as absent than full-pipeline runs would. Full-pipeline runs (calibration_v3) show lower absent counts after re-mapping.

**Criterion 2 (sparse → meaningful candidates): PASS.** Tropical geometry produces a 0.92 top candidate ("Tropical primitives Core" — 6 absent core types with 4 verified infra concepts). Combinatorial species correctly produces low-score (0.39), high-risk candidates reflecting zero Mathlib infrastructure.

**Criterion 3 (intermediate → partial-coverage candidates): PASS.** List operations scores higher (0.73) due to strong infrastructure (8 verified List.* concepts). Matroid theory scores lower (0.61) with weaker infrastructure (2 verified). Rankings correctly distinguish these situations.

**Criterion 4 (deterministic): PASS.** Two independent determinism tests (natural_number_addition, combinatorial_species) with fixed inputs produce byte-identical JSON output.

**Criterion 5 (inspectable): PASS.** Each candidate includes score_breakdown, justification, feasibility_notes, risk, and concept_statuses. A human can trace exactly why each candidate ranked where it is.

**Notable observations:**
- The partial weighting (0.5) works as intended: list_operations' mixed partial/absent clusters rank appropriately vs. matroid_theory's fully-absent clusters.
- Kind-based sub-splitting orphans parent types as singletons (e.g., `Species`, `GroupHom`) — documented as R1, deferred.
- The calibration_v3 group_homomorphisms run had a `related_verified` deduplication issue (duplicate `AddMonoidHom.comp`). Root cause: duplicate entries in the verification report from re-mapping. Defense-in-depth fix applied to `verified_names` collection in candidates.py.

---

## 11. Open Questions

1. **Should `partial` concepts be treated differently from `absent` concepts in clustering/scoring?** **Resolved.** Partial concepts are included in clustering (they are still under-covered), but they are weighted at 0.5 in the cluster size score while absent concepts are weighted at 1.0. The rationale is Mathlib novelty: an absent concept represents a genuine formalization opportunity, while a partial concept already has some Mathlib coverage. All else equal, a cluster dominated by absent concepts ranks higher than one dominated by partial concepts. The 0.5 weight is a default subject to calibration tuning.

2. **Should the cluster name be auto-generated or a placeholder?** The current design uses a simple heuristic (common namespace prefix + "Core"/"Extensions"). A better name could come from the concept kinds or from the original theme.

3. **How should `name_mismatch` concepts be handled?** They are currently excluded from pocket candidates (they exist, just under a different name). But a cluster of name_mismatch concepts might indicate a naming convention pocket -- a different kind of contribution opportunity.
