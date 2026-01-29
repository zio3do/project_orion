import Mathlib.Data.Nat.Basic

def hello := "world"

def add (a b : Nat) : Nat :=
  a + b

-- theorem add_comm (a b : Nat) : add a b = add b a := by simp [add, Nat.add_comm]
