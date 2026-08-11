import Mathlib

namespace MathlibPlus.Combinatorics.ThreeSunflower

/-- Claim 20850: an ordered triple is a three-sunflower exactly when every
pairwise intersection has the cardinality of the common triple intersection.
The left side is the standard set-theoretic formulation of the sunflower core. -/
theorem threeSunflower_iff_pairIntersectionCardEqTriple
    {α : Type*} [DecidableEq α]
    (A₁ A₂ A₃ : Finset α) :
    (A₁ ∩ A₂ = A₁ ∩ A₃ ∧ A₁ ∩ A₂ = A₂ ∩ A₃) ↔
      (A₁ ∩ A₂).card = (A₁ ∩ A₂ ∩ A₃).card ∧
      (A₁ ∩ A₃).card = (A₁ ∩ A₂ ∩ A₃).card ∧
      (A₂ ∩ A₃).card = (A₁ ∩ A₂ ∩ A₃).card := by
  constructor
  · rintro ⟨h₁₃, h₂₃⟩
    have h₁₂_tri : A₁ ∩ A₂ = A₁ ∩ A₂ ∩ A₃ := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hx₁₃ : x ∈ A₁ ∩ A₃ := by
          rw [← h₁₃]
          exact hx
        simp only [Finset.mem_inter] at hx hx₁₃ ⊢
        exact ⟨hx, hx₁₃.2⟩
      · intro x hx
        simp only [Finset.mem_inter] at hx ⊢
        exact hx.1
    have h₁₃_tri : A₁ ∩ A₃ = A₁ ∩ A₂ ∩ A₃ :=
      h₁₃.symm.trans h₁₂_tri
    have h₂₃_tri : A₂ ∩ A₃ = A₁ ∩ A₂ ∩ A₃ := by
      exact h₂₃.symm.trans h₁₂_tri
    exact ⟨congrArg Finset.card h₁₂_tri,
      congrArg Finset.card h₁₃_tri, congrArg Finset.card h₂₃_tri⟩
  · rintro ⟨h₁₂, h₁₃, h₂₃⟩
    have htri_sub_₁₂ : A₁ ∩ A₂ ∩ A₃ ⊆ A₁ ∩ A₂ := by
      intro x hx
      simp only [Finset.mem_inter] at hx ⊢
      exact hx.1
    have htri_sub_₁₃ : A₁ ∩ A₂ ∩ A₃ ⊆ A₁ ∩ A₃ := by
      intro x hx
      simp only [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    have htri_sub₂₃ : A₁ ∩ A₂ ∩ A₃ ⊆ A₂ ∩ A₃ := by
      intro x hx
      simp only [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1.2, hx.2⟩
    have h₁₂_tri : A₁ ∩ A₂ = A₁ ∩ A₂ ∩ A₃ := by
      symm
      exact Finset.eq_of_subset_of_card_le htri_sub_₁₂ h₁₂.le
    have h₁₃_tri : A₁ ∩ A₃ = A₁ ∩ A₂ ∩ A₃ := by
      symm
      exact Finset.eq_of_subset_of_card_le htri_sub_₁₃ h₁₃.le
    have h₂₃_tri : A₂ ∩ A₃ = A₁ ∩ A₂ ∩ A₃ := by
      symm
      exact Finset.eq_of_subset_of_card_le htri_sub₂₃ h₂₃.le
    exact ⟨h₁₂_tri.trans h₁₃_tri.symm, h₁₂_tri.trans h₂₃_tri.symm⟩

end MathlibPlus.Combinatorics.ThreeSunflower
