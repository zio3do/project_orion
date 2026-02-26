# Theme Guide: Graded Order Combinatorics

## Purpose

This document records verified tactic patterns, correct Mathlib API names, and
known pitfalls for the **Graded Order Combinatorics** theme in Project Orion.
Every recipe below was extracted from proofs that passed `lake env lean` with
zero errors, zero `sorry`, and zero `axiom` declarations. Nothing here is
guesswork.

Use this guide as a reference when proving lemmas in this theme. When a hint
says "use `Polynomial.coeff_sum`", check this guide first — the correct name
may differ.

---

## 1. Environment Summary

- **Lean 4 v4.29.0-rc2**, Mathlib imported via `import Mathlib`
- **Namespace:** `Orion.GradedOrderCombinatorics`
- **Coefficient ring for polynomials:** `ℕ` (natural numbers)
- **Grade function:** `grade ℕ : α → ℕ` (from `GradeOrder ℕ α` or `GradeMinOrder ℕ α`)
- **Level sets:** `Finset.univ.filter (fun x : α => grade ℕ x = k)`
- **Covering relation:** `· ⋖ ·` (CovBy), grade increments by exactly 1

---

## 2. Critical API Name Corrections

These are the **most common failure modes** — using a plausible but wrong name.

### Polynomial coefficient extraction

| What you want | WRONG name | CORRECT name |
|---|---|---|
| Distribute `.coeff` over `Finset.sum` | `Polynomial.coeff_sum` | **`Polynomial.finset_sum_coeff`** |
| Coefficient of `n • p` (nsmul) | `Polynomial.coeff_nsmul` (does not exist) | **`Polynomial.coeff_smul`** (via `simp_rw`) |
| Coefficient of `X ^ j` at index `k` | — | **`Polynomial.coeff_X_pow`** |
| Evaluate `Finset.sum` of polynomials | — | **`Polynomial.eval_finset_sum`** |

**Why `Polynomial.coeff_sum` fails:** `Polynomial.coeff_sum` operates on
`Polynomial.sum` (a method that iterates over the support of a single polynomial).
It does **not** operate on `Finset.sum` (a sum over an external index set).
These are completely different operations with confusingly similar names.

### Finset sum collapse

| Pattern in goal | WRONG lemma | CORRECT lemma |
|---|---|---|
| `∑ x ∈ s, if k = x then f x else 0` | `Finset.sum_ite_eq'` | **`Finset.sum_ite_eq`** |
| `∑ x ∈ s, if x = k then f x else 0` | `Finset.sum_ite_eq` | **`Finset.sum_ite_eq'`** |

The primed vs. unprimed variants swap which side of the equality the summation
variable is on. After `Polynomial.coeff_X_pow`, the condition is `k = x`
(fixed value on the left), so use `Finset.sum_ite_eq` (unprimed).

### Finset emptiness / nonemptiness / max

| What you want | CORRECT name |
|---|---|
| Filter produces empty set | **`Finset.filter_eq_empty_iff`** |
| Card of empty finset | **`Finset.card_eq_zero`** |
| Card > 0 from nonempty | **`Finset.card_pos.mpr`** |
| Finset is nonempty from witness | `⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩` |
| Max element of nonempty finset | **`Finset.max'`** (returns element, needs nonemptiness proof) |
| Max element is in the set | **`Finset.max'_mem`** |
| All elements ≤ max | **`Finset.le_max'`** |
| Image of nonempty is nonempty | **`Finset.image_nonempty.mpr`** |

### Polynomial natDegree

| What you want | CORRECT name |
|---|---|
| `natDegree ≤ n ↔ ∀ m > n, coeff m = 0` | **`Polynomial.natDegree_le_iff_coeff_eq_zero`** |
| `n ≤ natDegree` from `coeff n ≠ 0` | **`Polynomial.le_natDegree_of_ne_zero`** |
| `natDegree = n` from `natDegree ≤ n` and `coeff n ≠ 0` | **`Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`** |

**Warning:** `Polynomial.natDegree_le_of_forall_coeff_eq_zero` does NOT exist.
Use `Polynomial.natDegree_le_iff_coeff_eq_zero.mpr` instead.

---

## 3. The nsmul Trap (Polynomial ℕ)

When working with `Polynomial ℕ`, scalar multiplication `n • p` (where `n : ℕ`)
is `AddMonoid.nsmul`, not ring multiplication. This has several consequences:

1. **`smul_eq_mul`** converts `nsmul` to `*` — use this via `simp only`.
2. **After converting to `*`**, use `mul_ite`, `mul_one`, `mul_zero` to push
   multiplication inside `if-then-else`.
3. **`Polynomial.coeff_smul`** works for nsmul when used via `simp_rw` (it
   handles the coercion automatically), but NOT via `rw` (which needs exact
   syntactic match).

### Proven recipe for coefficient extraction

```lean
-- Goal: Polynomial.coeff (∑ j ∈ S, c_j • X ^ j) k = ...
unfold rankGenPoly  -- or whatever definition wraps the sum
rw [Polynomial.finset_sum_coeff]           -- distribute coeff over Finset.sum
simp_rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]  -- must be simp_rw, not rw
simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]       -- nsmul → mul → push inside ite
rw [Finset.sum_ite_eq]                     -- collapse sum (check prime vs unprimed!)
```

---

## 4. simp_rw vs rw vs simp only

This distinction is critical in this theme and caused multiple failed attempts.

| Tactic | When to use |
|---|---|
| `rw [lemma]` | Goal has the pattern at the **top level** (not under binders, lambdas, or Finset.sum bodies) |
| `simp_rw [lemma]` | Pattern is **under a binder** (inside `∑`, `∀`, `∃`, `fun x =>`, etc.) |
| `simp only [lemma]` | Need to **simplify** (possibly creating new redexes) rather than directional rewrite |

**Common mistake:** Using `rw [Polynomial.coeff_smul]` after distributing the
sum. The `coeff_smul` pattern is inside the sum body, so `rw` can't find it.
`simp_rw` is required.

**Another mistake:** Using `simp only [Polynomial.coeff_sum, ...]` to try to
do everything in one step. This fails because `Polynomial.coeff_sum` is the
wrong lemma (see Section 2), and even `Polynomial.finset_sum_coeff` may not
fire via `simp only` due to the term's elaborated form.

---

## 5. Verified Tactic Patterns (from compiled proofs)

### Pattern: Membership in a filter-based level set

```lean
-- Goal: x ∈ Finset.univ.filter (fun x => grade ℕ x = k) ↔ grade ℕ x = k
simp [Finset.mem_filter, Finset.mem_univ]
```

### Pattern: Disjointness of level sets

```lean
-- Goal: Disjoint (level α k₁) (level α k₂) given h : k₁ ≠ k₂
rw [Finset.disjoint_left]
intro x hx1 hx2
rw [level_mem_iff] at hx1 hx2
exact h (hx1.symm.trans hx2)
```

### Pattern: Nonemptiness of a filtered finset from an existential witness

```lean
-- Goal: (Finset.univ.filter (fun x => grade ℕ x = k)).Nonempty given h : ∃ x, grade ℕ x = k
obtain ⟨x, hx⟩ := h
exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
```

### Pattern: Union of level sets is the whole finset

```lean
-- Goal: Finset.biUnion (Finset.univ.image (grade ℕ)) (fun k => Finset.univ.filter ...) = Finset.univ
ext x
constructor
· intro _; exact Finset.mem_univ x
· intro _; apply Finset.mem_biUnion.mpr
  exact ⟨grade ℕ x, Finset.mem_image_of_mem (grade ℕ) (Finset.mem_univ x),
         Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
```

### Pattern: Sum of level cardinalities = total cardinality

```lean
-- Term-mode proof
exact (Finset.card_eq_sum_card_image (grade ℕ) (Finset.univ : Finset α)).symm.trans Finset.card_univ
```

### Pattern: Evaluating polynomial at a value (distributing eval over Finset.sum)

```lean
unfold rankGenPoly
rw [Polynomial.eval_finset_sum]
simp only [Polynomial.eval_smul, Polynomial.eval_pow, Polynomial.eval_X, ...]
```

Note: `Polynomial.eval_finset_sum` works with `rw` (unlike `finset_sum_coeff`
which also works with `rw`). Both are top-level patterns after `unfold`.

### Pattern: Grade increment via CovBy (covering relation)

```lean
-- Goal: grade ℕ a + 1 = grade ℕ b given hrel : a ⋖ b
exact Order.covBy_iff_add_one_eq.mp (hrel.grade (𝕆 := ℕ))
```

Note the explicit universe annotation `(𝕆 := ℕ)` — this is needed for
`CovBy.grade` to resolve the grade order typeclass.

### Pattern: Induction on covering chains (List.IsChain)

```lean
induction l with
| nil => exact absurd rfl hne  -- or contradiction
| cons a t ih =>
  cases t with
  | nil => simp
  | cons b rest =>
    have hne' : b :: rest ≠ [] := List.cons_ne_nil _ _
    have htail : (b :: rest).IsChain (· ⋖ ·) := List.IsChain.tail hl
    have hrel : a ⋖ b := List.IsChain.rel_head hl
    have ih' := ih htail hne'
    -- ... use ih', hrel, omega
```

Key API:
- `List.IsChain.tail` — tail of a chain is a chain
- `List.IsChain.rel_head` — extract the first covering relation
- `List.getLast_cons` — `(a :: b :: rest).getLast _ = (b :: rest).getLast _`

**IMPORTANT:** `List.Chain'` is deprecated (since 2025-09-19). Use `List.IsChain` instead.
Similarly, `List.chain'_singleton` → `List.isChain_singleton`,
`List.chain'_cons_cons` → `List.isChain_cons_cons`.

### Pattern: Constructing covering chains (cons_of_ne_nil)

```lean
-- Goal: (a :: l).IsChain (· ⋖ ·) given hchain : l.IsChain (· ⋖ ·), hne : l ≠ [],
--       and hac : a ⋖ l.head hne
exact List.IsChain.cons_of_ne_nil hne hchain hac
```

Key API:
- `List.IsChain.cons_of_ne_nil` — `l ≠ [] → IsChain R l → R x (l.head _) → IsChain R (x :: l)`
- `List.isChain_singleton` — `IsChain R [a]` (constructor, replaces deprecated `chain'_singleton`)
- `List.isChain_cons_cons` — `IsChain R (a :: b :: l) ↔ R a b ∧ IsChain R (b :: l)`

**Warning:** Do NOT use dot notation on `Chain'`-typed hypotheses for `IsChain` methods.
If `hchain : l.Chain' R` (which is `List.IsChain R l` under the hood), dot notation
like `hchain.cons_of_ne_nil` may fail because the elaborator sees the deprecated alias.
Use the full name: `List.IsChain.cons_of_ne_nil hne hchain hac`.

### Pattern: Strong induction on natural number gap

```lean
-- For proving ∀ a b, a ≤ b → P a b, by induction on grade ℕ b - grade ℕ a
suffices h : ∀ n, ∀ a b : α, a ≤ b → grade ℕ b - grade ℕ a = n → P a b from
  h _ a b hab rfl
intro n
induction n using Nat.strongRecOn with
| ind n ih =>
  intro a b hab hgap
  obtain rfl | hlt := eq_or_lt_of_le hab
  · -- Base case: a = b
    ...
  · -- Inductive case: a < b
    ...
```

**IMPORTANT:** `eq_or_lt_of_le` requires `[PartialOrder α]`, NOT just `[Preorder α]`.
In a `Preorder`, `a ≤ b ∧ b ≤ a` does NOT imply `a = b` (no antisymmetry).

### Pattern: Using IsStronglyAtomic to find covering elements

```lean
-- Given hlt : a < b, find c with a ⋖ c ∧ c ≤ b
obtain ⟨c, hac, hcb⟩ := exists_covBy_le_of_lt hlt
have hgac : grade ℕ c = grade ℕ a + 1 :=
  (Order.covBy_iff_add_one_eq.mp (hac.grade (𝕆 := ℕ))).symm
```

Key facts:
- `WellFoundedLT α` is **automatic** from `[GradeOrder ℕ α]` via a global instance
- `IsStronglyAtomic α` is **automatic** from `[WellFoundedLT α]` via a global instance
- `exists_covBy_le_of_lt : a < b → ∃ x, a ⋖ x ∧ x ≤ b` — provided by `IsStronglyAtomic`
- `Order.covBy_iff_add_one_eq` gives `a ⋖ b ↔ a + 1 = b` (note: result is `a + 1 = b`, use `.symm` for `b = a + 1`)
- `.grade (𝕆 := ℕ)` lifts `a ⋖ b` to `grade ℕ a ⋖ grade ℕ b`

### Pattern: natDegree of a finset sum of monomials (le_antisymm approach)

```lean
-- Goal: (∑ k ∈ S, c_k • X ^ k).natDegree = S.max' hS
-- where every c_k > 0 for k ∈ S
apply le_antisymm
· -- Upper bound: natDegree ≤ max'
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  -- show coeff at n is 0 using rankGenPoly_coeff + filter emptiness
  rw [rankGenPoly_coeff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  have : grade ℕ x ≤ m := Finset.le_max' S _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  omega
· -- Lower bound: max' ≤ natDegree
  apply Polynomial.le_natDegree_of_ne_zero
  -- show coeff at max' is nonzero using rankGenPoly_coeff + nonemptiness
  rw [rankGenPoly_coeff]
  -- extract witness from Finset.max'_mem, build filter membership
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩ |>.ne'
```

### Pattern: Closing ℕ arithmetic goals after grade equations

```lean
omega
```

After establishing grade equations like `grade(last) = grade(head) + (length - 1)`,
`omega` handles the remaining natural number arithmetic.

---

## 6. Typeclass Resolution Pitfalls

### GradeOrder vs GradeMinOrder

- `GradeOrder ℕ α` — provides `grade ℕ : α → ℕ`, used in level sets and rank-generating polynomial
- `GradeMinOrder ℕ α` — provides grade + covering chain properties, used in saturated chain lemmas
- These are **different typeclasses**. Check which one the lemma statement uses.

### Finset.univ type annotation

When `Finset.univ` appears in a context with multiple types (e.g., both `α` and
`ℕ`), Lean may fail to infer which universe to use. Annotate explicitly:

```lean
(Finset.univ : Finset α).image (grade ℕ)
--            ^^^^^^^^^^^ prevents ambiguity
```

This annotation was needed for `level_union` and `levelCard_sum`.

---

## 7. What NOT to Do

1. **Do not use `Polynomial.coeff_sum`** for distributing over `Finset.sum`. It
   is for `Polynomial.sum` (a different operation). Use `Polynomial.finset_sum_coeff`.

2. **Do not use `rw` for rewrites inside sum bodies.** Use `simp_rw`.

3. **Do not guess Mathlib lemma names.** Use LeanExplore to verify a name exists
   before using it. Hallucinated names are the #1 failure mode.

4. **Do not trust lean-lsp-mcp diagnostics as authoritative.** The LSP may show
   stale or incomplete diagnostics. The **only** authoritative check is
   `lake env lean <file>`. If the LSP says "no errors" but you have any doubt,
   your proof will be verified by `lake env lean` independently.

5. **Do not add unnecessary `noncomputable` to theorems.** Only definitions that
   use classical choice need `noncomputable`. Theorems are propositions and are
   always computable in the proof-irrelevance sense.

---

## 8. Remaining Lemmas: Tactical Notes

### RankGenPoly track (depends on existing `rankGenPoly_coeff`)

**`rankGenPoly_eval_zero`** (easy): Evaluate at 0. After `unfold rankGenPoly` +
`rw [Polynomial.eval_finset_sum]`, simplify `0 ^ k` — for `k > 0` the term
vanishes, for `k = 0` it's 1. Consider `zero_pow`, `Finset.sum_ite_eq`.

**`rankGenPoly_coeff_eq_zero`** (easy): If no element has grade `k`, the k-th
coefficient is 0. Direct from `rankGenPoly_coeff` + empty filter argument.
Likely: `rw [rankGenPoly_coeff]; rw [Finset.card_eq_zero]; rw [Finset.filter_eq_empty_iff]; ...`

**`rankGenPoly_natDegree`** — ✅ PROVED. Uses `le_antisymm` with
`Polynomial.natDegree_le_iff_coeff_eq_zero` (upper) and
`Polynomial.le_natDegree_of_ne_zero` (lower). See verified pattern above.

### SaturatedChains track (depends on existing `saturatedChain_length`)

**`grade_le_of_chain`** (easy): Apply `saturatedChain_length`, then `omega`
(since `grade(last) = grade(head) + (length - 1)` and `length ≥ 1`).

**`saturatedChain_length_const`** (easy): Apply `saturatedChain_length` to both
chains, equate, then `omega`.

**`saturatedChain_length_grade_diff`** (easy): From `saturatedChain_length` +
`grade_le_of_chain`, rearrange with `omega`.

**`saturatedChain_grade_strictMono`** (easy): Show `a ⋖ b → grade ℕ a < grade ℕ b`
via `Order.covBy_iff_add_one_eq`, then `List.Chain'.pairwise` with `lt_trans`.

**`saturatedChain_nodup`** (easy): From `saturatedChain_grade_strictMono`, derive
`Pairwise (· ≠ ·)` via grade injectivity of `<`, which gives `Nodup`.

**`saturatedChain_exists`** — ✅ PROVED. Strong induction on `grade ℕ b - grade ℕ a`.
Requires `[PartialOrder α]` (not just `[Preorder α]`). Uses `exists_covBy_le_of_lt`
from `IsStronglyAtomic` (automatic via `WellFoundedLT` from `GradeOrder ℕ`).
Key tactics: `Nat.strongRecOn`, `subst`, `List.IsChain.cons_of_ne_nil`,
`List.getLast_cons`. See verified patterns above.
