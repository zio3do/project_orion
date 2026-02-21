import Mathlib.Data.Nat.Basic

theorem test1 (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
