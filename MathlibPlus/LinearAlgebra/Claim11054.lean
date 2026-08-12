import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/-- An alternating bilinear map vanishes when both arguments lie on one line.
The source's ``coefficient line'' is represented by the explicit generator `v`. -/
theorem alternatingBilinearForm_restrict_line_zero_claim11054
    {K V W : Type*} [Field K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W]
    (B : V →ₗ[K] V →ₗ[K] W)
    (hB : ∀ v : V, B v v = 0)
    (v : V) (a b : K) :
    B (a • v) (b • v) = 0 := by
  rw [map_smul, map_smul]
  simp [hB]

/-- Every alternating bilinear map on a one-dimensional module is zero. -/
theorem rankOneAlternatingForm_vanishes_claim11054
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (B : V →ₗ[K] V →ₗ[K] W)
    (hB : ∀ v : V, B v v = 0)
    (hV : ∃ v : V, v ≠ 0 ∧ ∀ w : V, ∃ a : K, a • v = w) :
    B = 0 := by
  rcases hV with ⟨v, hv, hspan⟩
  ext x y
  obtain ⟨a, rfl⟩ := hspan x
  obtain ⟨b, rfl⟩ := hspan y
  exact alternatingBilinearForm_restrict_line_zero_claim11054 B hB v a b

end MathlibPlus.LinearAlgebra
