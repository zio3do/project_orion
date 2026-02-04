import Mathlib.Tactic

 --
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring


-- First Z Lean Proof
example: ∀ m n : Nat, n + m = m + n := by
  intros m n
  -- Let's prove by induction
  induction n with
  | zero =>
    -- Base case: when n = 0
    rw[Nat.add_zero]
    rw[Nat.zero_add]
    -- rw [Nat.zero_add, Nat.add_zero]
  | succ d hd =>
    -- Inductive case: assume it holds for d, prove for d + 1
    rw[← Nat.succ_eq_add_one]
    rw[Nat.succ_add]
    rw[Nat.add_succ]
    rw[Nat.succ_eq_add_one]
    rw[Nat.succ_eq_add_one]
    rw[hd]


-- Version 1: Using tactic mode
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq =>
    constructor
    · exact hq
    · exact hp

-- Version 2: Using term mode (pattern matching)
example (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
