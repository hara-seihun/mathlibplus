import Mathlib

namespace MathlibPlus.GroupTheory

/-- If the quotient action fixes the core orbit of `x`, then the full orbit is
that core orbit.  The set-level hypotheses are the explicit carrier for the
source's quotient-coset and translation action. -/
theorem quotientFixedCosetOrbit_claim39444
    {W : Type*} (Γ V : Set (W ≃ W)) (x : W)
    (hVΓ : V ⊆ Γ)
    (hfix : ∀ γ ∈ Γ, ∃ v ∈ V, γ x = v x) :
    {y | ∃ γ ∈ Γ, γ x = y} = {y | ∃ v ∈ V, v x = y} := by
  ext y
  constructor
  · rintro ⟨γ, hγ, hγy⟩
    rcases hfix γ hγ with ⟨v, hv, hvx⟩
    exact ⟨v, hv, hvx.symm.trans hγy⟩
  · rintro ⟨v, hv, hvy⟩
    exact ⟨v, hVΓ hv, hvy⟩

end MathlibPlus.GroupTheory
