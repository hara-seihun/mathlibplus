import Mathlib

namespace MathlibPlus.Combinatorics.Claim9186

/-- Exact-one membership makes a finite family of blocks a partition of its
finite ambient set. -/
theorem exact_one_membership_partition
    {α : Type*} [DecidableEq α]
    (X : Finset α)
    (B : Finset (Finset α))
    (hblocks : ∀ A ∈ B, A ⊆ X)
    (hexact : ∀ x ∈ X, ∃! A, A ∈ B ∧ x ∈ A) :
    (∀ A ∈ B, ∀ C ∈ B, A ≠ C → Disjoint A C) ∧
      B.biUnion id = X := by
  classical
  have hdisjoint : ∀ A ∈ B, ∀ C ∈ B, A ≠ C → Disjoint A C := by
    intro A hA C hC hAC
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hxX : x ∈ X := hblocks A hA hxA
    rcases hexact x hxX with ⟨D, hD, hDunique⟩
    have hAD : A = D := hDunique A ⟨hA, hxA⟩
    have hCD : C = D := hDunique C ⟨hC, hxC⟩
    exact hAC (hAD.trans hCD.symm)
  have hunion : B.biUnion id = X := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hA, hxA⟩
      exact hblocks A hA hxA
    · intro hx
      rcases hexact x hx with ⟨A, hA, _⟩
      exact Finset.mem_biUnion.mpr ⟨A, hA.1, hA.2⟩
  exact ⟨hdisjoint, hunion⟩

end MathlibPlus.Combinatorics.Claim9186
