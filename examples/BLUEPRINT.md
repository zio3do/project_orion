# Blueprint: Graded Order Combinatorics

Revision: v2.2-extended
Generated: 2026-02-25T18:25:16.990184+00:00
Corrected: 2026-02-25 (v2.1 manual audit)
Extended: 2026-02-25 (v2.2 extensions)
Theme document: library_architect/themes/graded_order_combinatorics.md

## Summary

- Definitions: 2 (level, rankGenPoly)
- Lemmas: 17
- Planned: 19
- Exists in Mathlib: 1 (level via Erdos1043.levelSet)
- Layers: 3

## Change Log

### v2.2 — Extensions (6 entries added)

| Entry | Layer | Description |
|---|---|---|
| `rankGenPoly_eval_zero` | 2 | Evaluating the rank-generating polynomial at 0 gives `|level 0|`. |
| `rankGenPoly_coeff_eq_zero` | 2 | If no element has grade k, the k-th coefficient is 0. Key helper for `rankGenPoly_natDegree`. |
| `grade_le_of_chain` | 3 | Grade of head ≤ grade of last in a covering chain. Guards ℕ subtraction. |
| `saturatedChain_length_grade_diff` | 3 | `l.length = grade(last) - grade(head) + 1`. Combinatorially natural form. |
| `saturatedChain_grade_strictMono` | 3 | Grades strictly increase along a covering chain. Foundation for nodup. |
| `saturatedChain_nodup` | 3 | Elements in a covering chain are distinct. Corollary of strict monotonicity. |

### v2.1 — Manual Audit (7 removed, 3 fixed, 1 added)

#### Removed (7 entries)

| Entry | Reason |
|---|---|
| `level_monotonicity` | **Mathematically false.** `|level_k| ≤ |level_{k+1}|` does not hold for general graded posets. |
| `level_covering` | **Type error.** Used `⋃` (Set.iUnion → Set α) but `level` returns `Finset α`. Redundant with `level_union`. |
| `rankGenPoly_simp` | **Placeholder.** Signature was `... := ...` with no actual statement. |
| `saturatedChain_length_eq` | **Redundant.** Same as `saturatedChain_length` but with ℕ subtraction that could underflow. |
| `saturatedChain` | **Malformed definition.** `l.head ≠ []` doesn't type-check; `hne` was unbound. The predicate `l.Chain' (· ⋖ ·)` is used directly in theorem hypotheses instead. |
| `maximalChain_in_saturated` | **Meaningless hypothesis.** `∀ x ∈ c, x` is not a proposition. Formalization requires Mathlib's `IsMaxChain` on sets, beyond this blueprint's scope. |
| `maximalChain_length_const` | **Replaced** by `saturatedChain_length_const`. Original used `Chain' (≤)` (too weak — statement is false for non-saturated chains). |

#### Fixed (3 entries)

| Entry | Fix |
|---|---|
| `level_disjoint` | Removed incorrect proof body `Finset.disjoint_filter_filter _ _ _` from signature. |
| `level_union` | Fixed informal description (was "covering relation", now "all level sets equal full finset"). Removed spurious `CovBy` dependency. Added `[DecidableEq α]` (required by `Finset.biUnion`). |
| `rankGenPoly_degree` | **Renamed to `rankGenPoly_natDegree`**. Uses `Polynomial.natDegree` (returns `ℕ`) instead of `Polynomial.degree` (returns `WithBot ℕ`). Fixed nonemptiness proof to `Finset.image_nonempty.mpr Finset.univ_nonempty`. Added `[Nonempty α]` precondition. |

#### Added in v2.1 (1 entry)

| Entry | Description |
|---|---|
| `saturatedChain_length_const` | All saturated chains between the same endpoints have the same length. Corrected replacement for `maximalChain_length_const` with `Chain' (· ⋖ ·)` hypotheses. |

## Dependency Graph

```
level ← GradeOrder, grade
level_mem_iff ← level
level_disjoint ← level, level_mem_iff
level_nonempty ← level
level_union ← level
level_card_sum ← level, level_disjoint, level_union
rankGenPoly ← level
rankGenPoly_eval_one ← rankGenPoly, level_card_sum
rankGenPoly_coeff ← rankGenPoly, level
rankGenPoly_natDegree ← rankGenPoly, rankGenPoly_coeff, level_nonempty
rankGenPoly_eval_zero ← rankGenPoly, rankGenPoly_coeff          [NEW]
rankGenPoly_coeff_eq_zero ← rankGenPoly_coeff                   [NEW]
saturatedChain_length ← CovBy, GradeMinOrder
saturatedChain_exists ← CovBy, GradeMinOrder
saturatedChain_length_const ← saturatedChain_length
grade_le_of_chain ← saturatedChain_length                       [NEW]
saturatedChain_length_grade_diff ← saturatedChain_length, grade_le_of_chain  [NEW]
saturatedChain_grade_strictMono ← CovBy, GradeMinOrder          [NEW]
saturatedChain_nodup ← saturatedChain_grade_strictMono           [NEW]
```

## Layer 1: Level Sets and Basic Properties

### DEF level

- status: exists_in_mathlib
- signature: `noncomputable def level (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) : Finset α := Finset.univ.filter (fun x => grade ℕ x = k)`
- informal: The level set of a graded poset at grade k: all elements with grade equal to k.
- grounding: exists (Erdos1043.levelSet)
- depends_on: GradeOrder, grade

### LEMMA level_mem_iff

- status: planned
- signature: `theorem level_mem_iff [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (x : α) (k : ℕ) : x ∈ level α k ↔ grade ℕ x = k`
- informal: Membership in a level set is equivalent to having the corresponding grade.
- depends_on: level
- hints: Unfold `level` and apply `Finset.mem_filter` and `Finset.mem_univ`.
- difficulty: easy

### LEMMA level_disjoint

- status: planned
- signature: `theorem level_disjoint [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] {k₁ k₂ : ℕ} (h : k₁ ≠ k₂) : Disjoint (level α k₁) (level α k₂)`
- informal: Level sets at different grades are disjoint.
- depends_on: level, level_mem_iff
- hints: Use `Finset.disjoint_filter.mpr` showing that `grade ℕ x = k₁` and `grade ℕ x = k₂` imply `k₁ = k₂`, contradicting `h`.
- difficulty: easy

### LEMMA level_nonempty

- status: planned
- signature: `theorem level_nonempty [Fintype α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) (h : ∃ x : α, grade ℕ x = k) : (Finset.univ.filter (fun x => grade ℕ x = k)).Nonempty`
- informal: If there exists an element with grade k, the level set at k is nonempty.
- depends_on: level
- hints: Obtain the witness from `h`, show it satisfies the filter predicate, then use `Finset.Nonempty.intro`.
- difficulty: easy

### LEMMA level_union

- status: planned
- signature: `theorem level_union [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Finset.biUnion ((Finset.univ : Finset α).image (grade ℕ)) (fun k => Finset.univ.filter (fun x => grade ℕ x = k)) = Finset.univ`
- informal: The union of all level sets equals the full finset.
- depends_on: level
- hints: Use `Finset.ext` and show membership in both directions.
- difficulty: easy

### LEMMA level_card_sum [Oracle-verified]

- status: planned
- signature: `theorem levelCard_sum [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : ∑ k ∈ (Finset.univ : Finset α).image (grade ℕ), (Finset.univ.filter (fun x : α => grade ℕ x = k)).card = Fintype.card α`
- informal: The sum of level set cardinalities equals the total cardinality of the type.
- depends_on: level, level_disjoint, level_union
- hints: Apply `(Finset.card_eq_sum_card_image (grade ℕ) Finset.univ).symm.trans Finset.card_univ`.
- difficulty: easy
- oracle_match: Orion/OracleTests/LevelCardSum.lean

## Layer 2: Rank Generating Polynomials

### DEF rankGenPoly [Oracle-verified]

- status: planned
- signature: `noncomputable def rankGenPoly (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Polynomial ℕ := ∑ k in (Finset.univ : Finset α).image (grade ℕ), (Finset.univ.filter (fun x : α => grade ℕ x = k)).card • (Polynomial.X ^ k)`
- informal: The rank-generating polynomial: coefficient at X^k is the cardinality of level k.
- depends_on: level
- oracle_match: Orion/OracleTests/RankGenPolyEvalOne.lean (definition)

### LEMMA rankGenPoly_eval_one [Oracle-verified]

- status: planned
- signature: `theorem rankGenPoly_eval_one (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Polynomial.eval 1 (rankGenPoly α) = Fintype.card α`
- informal: Evaluating the rank-generating polynomial at 1 gives the total cardinality.
- depends_on: rankGenPoly, level_card_sum
- hints: Unfold `rankGenPoly`, apply `Polynomial.eval_finset_sum`, `simp only [Polynomial.eval_smul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, smul_eq_mul, mul_one]`, then apply `levelCard_sum`.
- difficulty: medium
- oracle_match: Orion/OracleTests/RankGenPolyEvalOne.lean (theorem)

### LEMMA rankGenPoly_coeff

- status: planned
- signature: `theorem rankGenPoly_coeff (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) : Polynomial.coeff (rankGenPoly α) k = (Finset.univ.filter (fun x : α => grade ℕ x = k)).card`
- informal: The k-th coefficient of the rank-generating polynomial is the cardinality of level k.
- depends_on: rankGenPoly, level
- hints: Unfold `rankGenPoly`, apply `Polynomial.coeff_sum`, then use `Polynomial.coeff_smul` and `Polynomial.coeff_X_pow` to isolate the k-th term.
- difficulty: medium

### LEMMA rankGenPoly_natDegree

- status: planned
- signature: `theorem rankGenPoly_natDegree (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] [Nonempty α] : (rankGenPoly α).natDegree = ((Finset.univ : Finset α).image (grade ℕ)).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)`
- informal: The natural degree of the rank-generating polynomial is the maximum grade in the poset.
- depends_on: rankGenPoly, rankGenPoly_coeff, level_nonempty
- hints: Show the leading coefficient (at the max grade) is nonzero via `level_nonempty`, and all higher coefficients are zero via `rankGenPoly_coeff`.
- difficulty: hard

### LEMMA rankGenPoly_eval_zero [NEW in v2.2]

- status: planned
- signature: `theorem rankGenPoly_eval_zero (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Polynomial.eval 0 (rankGenPoly α) = ((Finset.univ : Finset α).filter (fun x : α => grade ℕ x = 0)).card`
- informal: Evaluating the rank-generating polynomial at 0 gives the cardinality of level 0.
- depends_on: rankGenPoly, rankGenPoly_coeff
- hints: Unfold `rankGenPoly`, apply `Polynomial.eval_finset_sum`, simplify `0^k` for `k > 0`. The only surviving term has `k = 0`.
- difficulty: easy

### LEMMA rankGenPoly_coeff_eq_zero [NEW in v2.2]

- status: planned
- signature: `theorem rankGenPoly_coeff_eq_zero (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) (h : ∀ x : α, grade ℕ x ≠ k) : Polynomial.coeff (rankGenPoly α) k = 0`
- informal: If no element has grade k, the k-th coefficient of the rank-generating polynomial is 0.
- depends_on: rankGenPoly_coeff
- hints: Rewrite via `rankGenPoly_coeff`. Show the filter is empty since `h` says no element has grade `k`. Apply `Finset.card_empty`.
- difficulty: easy

## Layer 3: Saturated Chains and Maximal Chains

### LEMMA saturatedChain_length [Oracle-verified]

- status: planned
- signature: `theorem saturatedChain_length [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) (hne : l ≠ []) : grade ℕ (l.getLast hne) = grade ℕ (l.head hne) + (l.length - 1)`
- informal: In a ℕ-graded order, a covering chain satisfies grade(last) = grade(head) + (length - 1).
- depends_on: CovBy, GradeMinOrder
- hints: Induction on `l`. Base: `nil` absurd, singleton `simp`. Cons case: extract `a ⋖ b`, apply IH on tail, use `CovBy.grade` and `Nat.covBy_iff_add_one_eq`, finish with `omega`.
- difficulty: hard
- oracle_match: Orion/OracleTests/SaturatedChainLength.lean

### LEMMA saturatedChain_exists

- status: planned
- signature: `theorem saturatedChain_exists [Preorder α] [GradeMinOrder ℕ α] (a b : α) (hab : a ≤ b) : ∃ l : List α, l ≠ [] ∧ l.Chain' (· ⋖ ·) ∧ l.head (by assumption) = a ∧ l.getLast (by assumption) = b`
- informal: A saturated (covering) chain exists between any two comparable elements.
- depends_on: CovBy, GradeMinOrder
- hints: Strong induction on `grade ℕ b - grade ℕ a`. Base case: `a = b`, return `[a]`. Inductive case: find `c` with `a ⋖ c` and `c ≤ b`, prepend `a` to chain from `c` to `b`.
- difficulty: hard

### LEMMA saturatedChain_length_const

- status: planned
- signature: `theorem saturatedChain_length_const [Preorder α] [GradeMinOrder ℕ α] (c₁ c₂ : List α) (hc₁ : c₁.Chain' (· ⋖ ·)) (hc₂ : c₂.Chain' (· ⋖ ·)) (hne₁ : c₁ ≠ []) (hne₂ : c₂ ≠ []) (hhead : c₁.head hne₁ = c₂.head hne₂) (hlast : c₁.getLast hne₁ = c₂.getLast hne₂) : c₁.length = c₂.length`
- informal: All saturated chains between the same endpoints have the same length.
- depends_on: saturatedChain_length
- hints: Apply `saturatedChain_length` to both chains. Equal endpoints force equal grade differences, so `c₁.length = c₂.length` by `omega`.
- difficulty: easy

### LEMMA grade_le_of_chain [NEW in v2.2]

- status: planned
- signature: `theorem grade_le_of_chain [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) (hne : l ≠ []) : grade ℕ (l.head hne) ≤ grade ℕ (l.getLast hne)`
- informal: In a covering chain, the grade of the head is at most the grade of the last element.
- depends_on: saturatedChain_length
- hints: Apply `saturatedChain_length` to get `grade(last) = grade(head) + (length - 1)`. Then `omega`.
- difficulty: easy

### LEMMA saturatedChain_length_grade_diff [NEW in v2.2]

- status: planned
- signature: `theorem saturatedChain_length_grade_diff [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) (hne : l ≠ []) : l.length = grade ℕ (l.getLast hne) - grade ℕ (l.head hne) + 1`
- informal: The length of a covering chain equals grade(last) - grade(head) + 1.
- depends_on: saturatedChain_length, grade_le_of_chain
- hints: Apply `saturatedChain_length` and `grade_le_of_chain`, then `omega`.
- difficulty: easy

### LEMMA saturatedChain_grade_strictMono [NEW in v2.2]

- status: planned
- signature: `theorem saturatedChain_grade_strictMono [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) : l.Pairwise (fun a b => grade ℕ a < grade ℕ b)`
- informal: Grades are strictly increasing along a covering chain.
- depends_on: CovBy, GradeMinOrder
- hints: Show `a ⋖ b → grade ℕ a < grade ℕ b` via `CovBy.grade` and `Nat.covBy_iff_add_one_eq`. Then use `List.Chain'.pairwise` with transitivity of `(<)`.
- difficulty: easy

### LEMMA saturatedChain_nodup [NEW in v2.2]

- status: planned
- signature: `theorem saturatedChain_nodup [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) : l.Nodup`
- informal: Elements in a covering chain are distinct (no duplicates).
- depends_on: saturatedChain_grade_strictMono
- hints: Apply `saturatedChain_grade_strictMono`. Show `grade a < grade b → a ≠ b`. Then `List.Pairwise.imp` gives `l.Pairwise (· ≠ ·)`, which is `l.Nodup`.
- difficulty: easy

## Mathematical Invariants

1. **Grade is a function**: Each element has exactly one grade. This makes level sets a partition.
2. **Covering = grade increment of 1**: In `GradeMinOrder ℕ`, `a ⋖ b` implies `grade ℕ a + 1 = grade ℕ b`.
3. **Level sets partition the poset**: `level_disjoint` + `level_union` together establish that `{level α k | k ∈ image grade ℕ univ}` is a partition of `Finset.univ`.
4. **Rank-generating polynomial encodes the partition**: `rankGenPoly_coeff` says the polynomial exactly encodes the level set sizes. `rankGenPoly_coeff_eq_zero` says unused grades contribute zero.
5. **Saturated chain length is determined by endpoints**: `saturatedChain_length_const` says the combinatorial distance between two elements is well-defined.
6. **Grades are strictly increasing along covering chains**: `saturatedChain_grade_strictMono` ensures no grade repetition, which implies `saturatedChain_nodup` (element distinctness).
7. **ℕ subtraction safety**: `grade_le_of_chain` guards the subtraction in `saturatedChain_length_grade_diff`, preventing silent underflow.

## Elaboration Status

All 19 entry signatures verified via `lake env lean Orion/ElabCheck/BlueprintV22.lean` with sorry bodies. 19/19 pass.
