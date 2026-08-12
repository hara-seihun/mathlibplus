import Mathlib

namespace MathlibPlus.GroupTheory.Claim58934

/--
For a finite graph block action this is the abstract group-theoretic core:
the full fiber over a prescribed block permutation is the right coset of the
block-action kernel through any chosen lift.
-/
theorem actualLiftFiber_eq_rightKernelCoset
    {G H : Type*} [Group G] [Group H]
    (ρ : G →* H) (f₀ : G) (q : H) (hq : ρ f₀ = q) :
    ρ ⁻¹' ({q} : Set H) = {g | ∃ k, ρ k = 1 ∧ g = k * f₀} := by
  ext g
  constructor
  · intro hg
    have hgq : ρ g = q := by simpa using hg
    refine ⟨g * f₀⁻¹, ?_, ?_⟩
    · simp [hgq, hq]
    · simp
  · rintro ⟨k, hk, rfl⟩
    simp [hk, hq]

end MathlibPlus.GroupTheory.Claim58934
