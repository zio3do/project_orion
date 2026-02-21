# Pocket Candidate Ranking — Ownership Transfer Document

*Phase 3 artifact per AGENTS.md. Written as an onboarding guide for an engineer who will maintain or extend the candidate ranking subsystem independently.*

---

## 1. What This Subsystem Does

The pocket candidate ranking layer (Module 4) is the final stage of the Edge Finder pipeline. Its job is to answer a single question: **given the absent and partial concepts identified by the verification layer, which clusters of related concepts represent the most promising mini-library contribution opportunities?**

It receives the outputs of Modules 1-3 — a `VerificationReport`, a `DensityReport`, a `GapReport`, the original concepts dict, and the full set of `SearchResponse` objects — and produces a `CandidateReport` containing a ranked list of pocket candidates. Each candidate is a cluster of related under-covered concepts with a composite score, human-readable justification, feasibility notes, and a risk assessment.

The subsystem is **purely algorithmic**. It makes no LLM or API calls. Given identical inputs, it produces byte-identical output. This was a deliberate design decision: the previous Module 4 (Pocket Synthesis) used an LLM to generate pocket descriptions and produced outputs that were fluent but ungrounded. The replacement trades narrative richness for auditability and determinism.

---

## 2. Mental Model for Understanding It

Think of Module 4 as a three-stage funnel:

```
VerificationReport
      │
      ▼
[1] Extract          Pull out every absent/partial concept as a flat list
      │
      ▼
[2] Cluster          Group by namespace prefix; sub-split large groups by kind
      │
      ▼
[3] Score & Rank     Three-factor scoring; sort descending; assign ranks
      │
      ▼
CandidateReport
```

The clustering logic is the most consequential stage. The scoring reflects the clustering — if the clustering is wrong, the scores are meaningless. The key insight is that namespace prefix is used as a proxy for mathematical relatedness: `Tropical.*` concepts are presumed to belong together, and `List.*` concepts belong together separately.

**The partial weighting principle:** a cluster of entirely absent concepts scores higher than a cluster of the same size with partial concepts. The reasoning is Mathlib novelty — absent concepts represent genuine formalization opportunities; partial concepts already have some Mathlib foothold. This is encoded in `PARTIAL_WEIGHT = 0.5`, applied during cluster size scoring.

**What the score does and does not mean:** the composite score (0.0–1.0) is a relative ordering signal, not an absolute quality judgment. A score of 0.92 does not mean the pocket is 92% likely to be a good contribution. It means that candidate ranked significantly higher than one scoring 0.40 on the three factors. Human judgment is required to interpret the output.

---

## 3. Directory Structure

```
edge_finder/edge_finder/analysis/
    candidates.py    The entire subsystem (533 lines)
                     Contains: constants, data model, all three pipeline steps,
                     scoring helpers, and the top-level rank_candidates() entry point.
    __init__.py      Exports candidates in __all__
    density.py       Upstream: DensityReport (consumed but not modified by this module)
    heuristics.py    Upstream: GapReport (consumed but not modified by this module)

edge_finder/docs/candidate_ranker/
    edge_finder_pocket_candidates.md    Phase 1 design document + calibration results
    CANDIDATES_WALKTHROUGH.md           This document
```

There is no further subdivision. The module is 533 lines but approximately 160 lines of that is docstrings, comments, and blank lines. No single function exceeds 45 lines.

**Upstream dependencies (inputs):**

```
edge_finder.verification      VerificationReport, VerificationStatus, ConceptKind
edge_finder.analysis.density  DensityReport
edge_finder.analysis.heuristics  GapReport
edge_finder.search.models     SearchResponse (accepted but not used in v1.0 scoring)
```

**Downstream consumers:**

```
cli.py          calls rank_candidates(), serializes CandidateReport to candidates.json
```

Note: `SearchResponse` is accepted as a parameter for forward-compatibility (future scoring factors may use search result data) but is not used in the current scoring logic.

---

## 4. Call Graph

```
cli.main()
  │
  └─► rank_candidates(verification, density, gap, concepts, responses, theme)
          │
          ├─ extract_under_covered(verification)
          │      │
          │      └─ for each entry in verification.entries:
          │             if status in {ABSENT, PARTIAL}:
          │                 _namespace_prefix(entry.concept)  →  namespace_prefix
          │                 → UnderCoveredConcept
          │         → list[UnderCoveredConcept]
          │
          ├─ [build verified_names: sorted set of verified entry.concept strings]
          │
          ├─ cluster_concepts(under_covered)
          │      │
          │      ├─ group by namespace_prefix.lower()  (case-insensitive merge)
          │      │
          │      ├─ for groups with len < MIN_CLUSTER_SIZE (2):
          │      │       → unclustered
          │      │
          │      ├─ for groups with len > KIND_SPLIT_THRESHOLD (5):
          │      │       sub-split by ConceptKind
          │      │       kind sub-groups < MIN_CLUSTER_SIZE → unclustered
          │      │       kind sub-groups >= MIN_CLUSTER_SIZE → ConceptCluster
          │      │
          │      └─ for groups with 2 <= len <= 5:
          │              → ConceptCluster (no sub-splitting)
          │         → (list[ConceptCluster], list[str] unclustered)
          │
          ├─ _extract_gap_confidence(gap)
          │
          └─ for each cluster:
                 score_cluster(cluster, verified_names, gap_confidence)
                     │
                     ├─ [cluster size score]  absent + 0.5*partial / MAX_EFFECTIVE_SIZE
                     │
                     ├─ [infra proximity score]
                     │       filter verified_names by namespace prefix match
                     │       len(related) / MAX_RELATED_VERIFIED
                     │
                     ├─ [coherence score]
                     │       0.5 * primitive_ratio
                     │     + 0.5 * name_similarity  (_avg_pairwise_lcp / avg_name_len)
                     │
                     ├─ [composite]  0.30*size + 0.35*infra + 0.35*coherence
                     │
                     ├─ _generate_name(prefix, concepts)
                     ├─ _generate_justification(...)
                     ├─ _generate_feasibility_notes(...)
                     └─ _assess_risk(gap_confidence, infra_score)
                 → ScoredCandidate (rank=0)

             sort by score descending
             assign ranks 1..N
             → CandidateReport
```

---

## 5. Execution Lifecycle Walkthrough

### Step 1: Extract under-covered concepts

`extract_under_covered()` iterates over `verification.entries` and selects every entry with status `ABSENT` or `PARTIAL`. For each, it calls `_namespace_prefix()` to determine the clustering key, then wraps it as an `UnderCoveredConcept`.

**`_namespace_prefix()` is the most consequential single function in this module.** It determines which cluster a concept ends up in. The logic, in order:

1. Strip everything after the first dot: `TropicalCurve.forward_image` → `TropicalCurve`
2. PascalCase split at the first uppercase boundary after position 3: `TropicalCurve` → `Tropical`
3. If no PascalCase boundary found, snake_case fallback: `tropical_sum` → `tropical`
4. If no underscore, return the base as-is: `Nat` → `Nat`

The position-3 guard prevents over-splitting short names: `Add` remains `Add` rather than splitting at `A`.

### Step 2: Cluster by namespace prefix

`cluster_concepts()` groups concepts into a `defaultdict` keyed by lowercased prefix. This case-insensitive merge ensures `Tropical` and `tropical` land in the same cluster.

Three outcomes per group:

- **Too small (< 2):** dissolved into `unclustered_concepts`. A lone absent concept is a gap, not a pocket.
- **Too large (> 5):** sub-split by `ConceptKind`. Primitives get their own sub-cluster, operators get their own, identity families get their own. Sub-clusters that are still too small after splitting are dissolved into unclustered.
- **Just right (2–5):** promoted directly to a `ConceptCluster`.

The kind-based sub-splitting produces cluster names like `Tropical (primitives)` vs. `Tropical (operators)`. The suffix pluralization logic handles the `identity_family` → `identity families` conversion (and avoids `identity familys`).

### Step 3: Score each cluster

`score_cluster()` computes three sub-scores, each normalised to [0, 1], then combines them.

**Cluster size score (weight 0.30):**
```
effective_size = count(absent) + 0.5 * count(partial)
size_score = min(effective_size / 5, 1.0)
```
Saturates at 5 effective concepts. The `0.5` discount on partial concepts encodes the Mathlib novelty principle.

**Infrastructure proximity score (weight 0.35):**
```
related = verified concepts whose namespace_prefix matches this cluster's prefix
infra_score = min(len(related) / 3, 1.0)
```
Saturates at 3 related verified concepts. This rewards building adjacent to existing Mathlib infrastructure rather than starting from scratch.

**Concept coherence score (weight 0.35):**
```
coherence = 0.5 * primitive_ratio + 0.5 * name_similarity
```
`primitive_ratio` is the fraction of concepts that are primitives (types, structures). A cluster of core types scores higher than a cluster of lemmas, reflecting the intuition that a mini-library starts with its foundational types. `name_similarity` is the average pairwise longest common prefix length divided by average name length — a proxy for whether the concepts "look like" they belong together lexically.

**Composite:**
```
score = 0.30 * size_score + 0.35 * infra_score + 0.35 * coherence_score
```

After scoring, candidates are sorted descending by score and ranks 1..N are assigned. Because `ScoredCandidate` is a frozen dataclass, rank assignment requires reconstructing the object.

---

## 6. Annotated Excerpts of Key Functions

### `_namespace_prefix()` — line 142

```python
def _namespace_prefix(name: str) -> str:
```

This function is called once per concept during extraction and once per verified concept name during scoring. Both call paths must agree on what prefix a given string maps to — otherwise a verified concept and its under-covered neighbours could end up in different buckets and the infrastructure proximity score would be silently wrong.

**Known limitation:** names that don't follow PascalCase or snake_case conventions produce unexpected prefixes. `GroupHom` splits at position 5 → `Group`, which is correct. But a name like `AddMonoidHom` splits at position 3 (`Add`) rather than at `Monoid` (position 3 is `d`, not uppercase). This is intentional: the position-3 guard means `Add` is treated as the top-level namespace, consistent with how Mathlib organises additive structures.

### `cluster_concepts()` — line 191

```python
def cluster_concepts(concepts) -> tuple[list[ConceptCluster], list[str]]:
```

The `sorted(groups.items())` on line 213 is load-bearing for determinism. Without it, the order of cluster processing would depend on dict insertion order, which is stable in Python 3.7+ but semantically arbitrary. The sort ensures alphabetical cluster ordering, which in turn determines the order in which clusters are scored (though ranking by score makes the scoring order irrelevant to the final output).

**The kind-split orphaning problem (Risk R1):** when a cluster is large enough to trigger kind-based splitting, the parent type often appears as a lone primitive. For example, `GroupHom` is a primitive, while `GroupHom.ker`, `GroupHom.image`, etc. are operators. After kind-split, `GroupHom` is a singleton primitive and gets relegated to unclustered. This is a known limitation, documented in the design doc and deferred.

### `score_cluster()` — line 366

```python
def score_cluster(cluster, verified_names, gap_confidence) -> ScoredCandidate:
```

**Line 385:** `cluster_prefix = cluster.namespace_prefix.split(" (")[0]`

This strips the kind suffix added during sub-clustering (e.g., `"Tropical (primitives)"` → `"Tropical"`). The infrastructure proximity lookup must use the bare prefix to match against `verified_names` correctly. If this strip is removed, sub-clustered candidates will never find any related verified concepts and will always score 0.0 on infrastructure proximity.

**Lines 386-392:** `related` is built with `sorted(set(...))`. The `set()` removes duplicates that arise when `verified_names` contains the same concept twice (which can happen if the verification report has duplicate entries from re-mapping). The `sorted()` ensures deterministic output ordering.

### `rank_candidates()` — line 446

```python
def rank_candidates(*, verification, density, gap, concepts, responses, theme) -> CandidateReport:
```

The early-return on line 466 handles the case where all concepts are verified — no under-covered concepts means no candidates. This is the expected path for a perfectly well-covered theme.

**Lines 483-489:** `verified_names` is built as a `sorted(set(...))` rather than a plain list. This defends against duplicate entries in the verification report (see Section 7, Invariant 4).

---

## 7. Critical Invariants

1. **`_namespace_prefix()` must be called identically for both under-covered concepts and verified concept names.** Both use the same function. If a parallel prefix extraction path is ever introduced for either, the infrastructure proximity score will silently produce wrong results.

2. **`cluster_prefix = cluster.namespace_prefix.split(" (")[0]` in `score_cluster()` must strip the kind suffix before the namespace prefix comparison.** Sub-clustered candidates have prefixes like `"Tropical (primitives)"`. Without stripping, no verified concept's prefix will match and infrastructure proximity will always be 0.

3. **`MIN_CLUSTER_SIZE = 2` enforces that a pocket is at least two concepts.** A single absent concept is a gap, not a pocket. Lowering this threshold would produce many single-concept candidates, defeating the clustering purpose.

4. **`verified_names` must be deduplicated before being used in `score_cluster()`.** The verification report can contain duplicate entries (same concept name appearing as both an operator and identity_family, or from two search passes). The `sorted(set(...))` on lines 483-489 ensures this. The downstream `set()` in `score_cluster()` provides a second layer of defence.

5. **Scoring weights must sum to 1.0.** `WEIGHT_CLUSTER_SIZE + WEIGHT_INFRA_PROXIMITY + WEIGHT_COHERENCE = 0.30 + 0.35 + 0.35 = 1.0`. If weights are changed, this invariant must be maintained or scores will not be interpretable as a 0–1 composite.

6. **The `scoring_version` metadata field must be bumped if the scoring formula changes.** Stored `candidates.json` files from different scoring versions are not comparable. The field exists precisely to flag version mismatches.

---

## 8. Things That Must Not Be Broken

- **The `_namespace_prefix()` function's PascalCase split boundary.** The position-3 guard (`i >= 3`) prevents short names like `Add` from being over-split. Removing it would change how `AddGroupHom`, `AddMonoid`, and similar names are clustered, silently reassigning concepts to different candidates.

- **The `set()` + `sorted()` pattern in `score_cluster()` for the `related` list.** Without `set()`, duplicate verified names produce inflated `len(related)` counts, which inflates `infra_score`, which inflates the composite score. A candidate could falsely appear to have strong infrastructure.

- **The `score_breakdown` field format in `to_dict()`.** The breakdown uses the weighted sub-score values (`WEIGHT_X * score_X`), not the raw sub-scores. This means `sum(score_breakdown.values()) == total_score`. If raw sub-scores are ever stored instead, the sum-check invariant breaks and the breakdown becomes misleading.

- **The `CandidateReport.to_dict()` output schema.** Downstream tooling reads `candidates.json` expecting specific field names (`rank`, `concepts`, `concept_statuses`, `score_breakdown`, etc.). Field renames break any script that reads these files.

- **The frozen dataclass pattern.** `ScoredCandidate` and `CandidateReport` are frozen. This guarantees they are not mutated after construction. The rank-assignment step in `rank_candidates()` reconstructs `ScoredCandidate` objects rather than mutating them. If the frozen constraint is removed for convenience, mutability bugs become possible in future extensions.

---

## 9. Most Dangerous Refactor Mistakes

1. **Changing `_namespace_prefix()` without auditing both call sites.** It is called during concept extraction (to assign cluster keys) and during scoring (to match verified names against cluster prefixes). Both must agree. Changing the function changes cluster membership and infrastructure proximity simultaneously, with no obvious test signal.

2. **Removing `cluster_prefix = cluster.namespace_prefix.split(" (")[0]` in `score_cluster()`. ** All sub-clustered candidates (any theme with > 5 concepts in a namespace) would score 0.0 on infrastructure proximity and rank at the bottom. The failure is silent — the output would still be valid JSON.

3. **Changing `MIN_CLUSTER_SIZE` or `KIND_SPLIT_THRESHOLD` without re-running calibration.** These constants control which concepts become candidates and which are orphaned. Changing them shifts the entire candidate set. The calibration results in the design doc (Section 10) are only valid for the current values `(2, 5)`.

4. **Changing scoring weights without bumping `scoring_version`.** Old `candidates.json` files stored on disk will have scores under the old formula. If scores from different runs are ever compared, version mismatch will silently corrupt the comparison.

5. **Adding `DensityReport` or `SearchResponse` data to scoring without documenting it.** Both are currently accepted as parameters but unused. They exist for forward-compatibility. Using them without documentation would make the scoring non-transparent — a human reading the score breakdown would not understand why two identical-looking clusters scored differently.

6. **Sorting `scored` in place and then iterating for rank assignment in the same loop.** The current code sorts `scored` then re-constructs ranked candidates in a separate loop. Collapsing these into a single loop with an `enumerate` on an unsorted list would produce arbitrary ranks.

---

## 10. Open Questions and Technical Debt

### Open questions

- **Singleton promotion for parent types (Risk R1).** The kind-split orphaning problem means the parent type of a large namespace cluster (e.g., `Species`, `GroupHom`) is consistently relegated to `unclustered_concepts`. A singleton-promotion rule — "if a concept is a primitive and its namespace has two or more clustered sub-concepts, promote it into the core cluster" — would address this. Deferred pending evidence that this actually matters for real contribution decisions.

- **Are the scoring weights empirically calibrated?** The `0.30/0.35/0.35` split is a reasonable default, not derived from data. Calibration runs so far suggest the weights produce sensible rankings, but a systematic weight search (e.g., holding out one theme and optimising weights against human judgment) has not been done.

- **Should `name_mismatch` concepts be included as candidates?** They are currently excluded entirely — a `name_mismatch` concept is treated as "found under a different name" and is neither extracted nor clustered. But a cluster of name_mismatch concepts might indicate a naming convention gap — a different kind of contribution opportunity (renaming or aliasing rather than new formalization). This is tracked as open question 3 in the design doc.

- **Should `SearchResponse` data feed into scoring?** The responses parameter is currently unused. One natural use: count how many search results mention a concept in `source_text` (not just `result.name`) as a proxy for "this concept is actively used in proofs even if not a top-level declaration". This would partially address the false-negative problem observed for structural lemmas like `Nat.add_assoc`.

### Technical debt

- **No tests.** The entire module has zero test coverage. The most important test cases:
  - `_namespace_prefix()`: PascalCase splits, snake_case fallback, short names, dot-separated.
  - `cluster_concepts()`: singleton dissolution, kind-split trigger, kind orphaning.
  - `score_cluster()`: weight arithmetic, infra score saturation, coherence edge cases.
  - `rank_candidates()`: empty under-covered list, all-partial cluster, all-absent cluster.
  - Determinism: two calls with identical inputs produce byte-identical JSON.

- **No `from_dict()` on `CandidateReport` or `ScoredCandidate`.** The stored `candidates.json` cannot be reloaded and re-processed without re-running the pipeline. This means Module 4 cannot currently be run in isolation against a previous run's outputs, even though all the necessary data is present on disk.

- **`_avg_pairwise_lcp()` is O(n²) in the number of concepts per cluster.** For the current cluster sizes (2–8 concepts), this is negligible. If cluster sizes grow substantially (e.g., a theme with 50 absent concepts in one namespace), this becomes a bottleneck.

- **`DensityReport` is accepted but unused.** It was included in the function signature for forward-compatibility. Either use it or remove it in a future iteration to reduce API surface. Keeping an unused parameter is a maintenance liability.

- **The coherence score's `name_similarity` component rewards lexical similarity, not mathematical relatedness.** `Nat.add_assoc` and `Nat.add_succ` score high on name similarity because they share the `Nat.add_` prefix. `TropicalPoint` and `TropicalFan` score lower despite being closely related mathematically. This is a known limitation of the purely algorithmic approach — acknowledged in the design doc (Risk R1).
