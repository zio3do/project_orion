# Theme: Graded Order Combinatorics

## What This Theme Is

Finite graded posets — finite posets equipped with a rank function that assigns a natural
number grade to each element, increasing by exactly 1 across each covering relation — are
a central object in combinatorics. Mathlib has a well-developed `GradeOrder` typeclass and
a rich covering relation (`CovBy`) API. It does not have the combinatorial layer that sits
on top of them: named level sets, rank generating functions, and structural results about
saturated chains and maximal chains.

This theme fills that gap — the missing connective tissue between Mathlib's order-theoretic
infrastructure for graded posets and finite combinatorics.

---

## Why It Is a Good Theme

**Partial infrastructure exists (~40–60% coverage).**
`GradeOrder`, `grade`, `CovBy`, `Fintype`, and `Finset` are all present and stable.
The work is extension, not greenfield construction.

**The gap is demonstrably real.**
Three already-proved oracle tests (`LevelCardSum`, `RankGenPolyEvalOne`,
`SaturatedChainLength`) each had to express their core concepts inline — level sets as
repeated `Finset.filter` expressions, rank polynomials as unnamed local definitions —
because no reusable abstraction existed. A proper library would make all three trivial.

**Structural and reusable, not arithmetic accumulation.**
The deliverable is a small set of definitions (`level`, `rankGenPoly`) and a collection of
lemmas that follow from them. This demonstrates operator thinking and abstraction taste,
not just identity-formula bookkeeping.

**Matches the target mathematical zone.**
Pure discrete mathematics and order theory on finite posets. No heavy abstract algebra,
no linear algebra. The hardest tools required are `Finset` combinatorics, `GradeOrder`
typeclass machinery, and induction over lists. All within reach.

**Connects two existing Mathlib subsystems.**
`GradeOrder` (in `Mathlib.Order`) and `Finset`/`Fintype` combinatorics (in
`Mathlib.Combinatorics`) are largely disconnected. This theme builds the bridge.


## Lemmas Promoted From Oracle Tests

| Oracle Test File | Promoted To |
|---|---|
| `Orion/OracleTests/LevelCardSum.lean` | Layer 1: `level_card_sum` |
| `Orion/OracleTests/RankGenPolyEvalOne.lean` | Layer 2: `rankGenPoly_eval_one` (rank generating function at 1) |
| `Orion/OracleTests/SaturatedChainLength.lean` | Layer 3: `saturatedChain_length` |

---

## What This Theme Is Not

- It does not attempt Dilworth's theorem or the LYM inequality. Those require significantly
  more infrastructure and belong to a future, more ambitious pocket.
- It does not attempt the "all maximal chains have equal length" characterization of graded
  posets as an equivalence theorem. That is a natural capstone result but is not
  load-bearing for this library.
- It does not touch the Möbius function or incidence algebras.

The theme is intentionally bounded. The goal is a coherent, well-documented mini-library
that demonstrates taste in abstraction — not the largest possible scope.
