/-
  Orion/OracleTests/FwdDiffMul.lean

  Novelty test for the Proof Oracle: the discrete product rule.
  Δ(fg)(n) = f(n+1)·Δg(n) + g(n)·Δf(n)

  This theorem does NOT exist in Mathlib (verified via LeanExplore).
  It requires genuine proof synthesis, not just a Mathlib lookup.

  The proof should follow from unfolding fwdDiff and ring arithmetic.
-/

import Mathlib

namespace Orion.OracleTests.FwdDiffMul

/-- The forward difference operator: Δf(n) = f(n+1) - f(n). -/
def fwdDiff (f : ℕ → ℤ) (n : ℕ) : ℤ := f (n + 1) - f n

/-- Discrete product rule: Δ(fg)(n) = f(n+1)·Δg(n) + g(n)·Δf(n). -/
theorem fwdDiff_mul (f g : ℕ → ℤ) (n : ℕ) :
    fwdDiff (fun i => f i * g i) n = f (n + 1) * fwdDiff g n + g n * fwdDiff f n := by
  simp [fwdDiff]; ring

end Orion.OracleTests.FwdDiffMul
