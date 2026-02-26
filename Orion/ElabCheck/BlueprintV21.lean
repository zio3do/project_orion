/-
  Elaboration check for corrected Graded Order Combinatorics blueprint v2.1.
  Each signature is wrapped in a section with sorry body.
  Run via: lake env lean Orion/ElabCheck/BlueprintV21.lean
-/
import Mathlib

-- @@ELAB_CHECK: level
section
noncomputable def level (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) : Finset α := Finset.univ.filter (fun x => grade ℕ x = k)
end

-- @@ELAB_CHECK: level_mem_iff
section
variable {α : Type*}
theorem level_mem_iff [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (x : α) (k : ℕ) : x ∈ level α k ↔ grade ℕ x = k := by
  sorry
end

-- @@ELAB_CHECK: level_disjoint
section
variable {α : Type*}
theorem level_disjoint [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] {k₁ k₂ : ℕ} (h : k₁ ≠ k₂) : Disjoint (level α k₁) (level α k₂) := by
  sorry
end

-- @@ELAB_CHECK: level_nonempty
section
variable {α : Type*}
theorem level_nonempty [Fintype α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) (h : ∃ x : α, grade ℕ x = k) : ((Finset.univ : Finset α).filter (fun x => grade ℕ x = k)).Nonempty := by
  sorry
end

-- @@ELAB_CHECK: level_union
section
variable {α : Type*}
theorem level_union [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Finset.biUnion ((Finset.univ : Finset α).image (grade ℕ)) (fun k => (Finset.univ : Finset α).filter (fun x => grade ℕ x = k)) = (Finset.univ : Finset α) := by
  sorry
end

-- @@ELAB_CHECK: levelCard_sum
section
variable {α : Type*}
theorem levelCard_sum [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : ∑ k ∈ (Finset.univ : Finset α).image (grade ℕ), ((Finset.univ : Finset α).filter (fun x : α => grade ℕ x = k)).card = Fintype.card α := by
  sorry
end

-- @@ELAB_CHECK: rankGenPoly
section
noncomputable def rankGenPoly (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Polynomial ℕ :=
  ∑ k ∈ (Finset.univ : Finset α).image (grade ℕ), ((Finset.univ : Finset α).filter (fun x : α => grade ℕ x = k)).card • (Polynomial.X ^ k)
end

-- @@ELAB_CHECK: rankGenPoly_eval_one
section
variable {α : Type*}
theorem rankGenPoly_eval_one (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] : Polynomial.eval 1 (rankGenPoly α) = Fintype.card α := by
  sorry
end

-- @@ELAB_CHECK: rankGenPoly_coeff
section
variable {α : Type*}
theorem rankGenPoly_coeff (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] (k : ℕ) : Polynomial.coeff (rankGenPoly α) k = ((Finset.univ : Finset α).filter (fun x : α => grade ℕ x = k)).card := by
  sorry
end

-- @@ELAB_CHECK: rankGenPoly_natDegree
section
variable {α : Type*}
theorem rankGenPoly_natDegree (α : Type*) [Fintype α] [DecidableEq α] [Preorder α] [GradeOrder ℕ α] [Nonempty α] : (rankGenPoly α).natDegree = ((Finset.univ : Finset α).image (grade ℕ)).max' (Finset.image_nonempty.mpr Finset.univ_nonempty) := by
  sorry
end

-- @@ELAB_CHECK: saturatedChain_length
section
variable {α : Type*}
theorem saturatedChain_length [Preorder α] [GradeMinOrder ℕ α] (l : List α) (hl : l.Chain' (· ⋖ ·)) (hne : l ≠ []) : grade ℕ (l.getLast hne) = grade ℕ (l.head hne) + (l.length - 1) := by
  sorry
end

-- @@ELAB_CHECK: saturatedChain_exists
section
variable {α : Type*}
theorem saturatedChain_exists [Preorder α] [GradeMinOrder ℕ α] (a b : α) (hab : a ≤ b) : ∃ l : List α, ∃ (hne : l ≠ []), l.Chain' (· ⋖ ·) ∧ l.head hne = a ∧ l.getLast hne = b := by
  sorry
end

-- @@ELAB_CHECK: saturatedChain_length_const
section
variable {α : Type*}
theorem saturatedChain_length_const [Preorder α] [GradeMinOrder ℕ α] (c₁ c₂ : List α) (hc₁ : c₁.Chain' (· ⋖ ·)) (hc₂ : c₂.Chain' (· ⋖ ·)) (hne₁ : c₁ ≠ []) (hne₂ : c₂ ≠ []) (hhead : c₁.head hne₁ = c₂.head hne₂) (hlast : c₁.getLast hne₁ = c₂.getLast hne₂) : c₁.length = c₂.length := by
  sorry
end
