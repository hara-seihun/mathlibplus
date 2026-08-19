import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim27431

/-- Vanishing of the relative derivative coefficient makes the normalized
scalar shear the identity on the specified semidirect-product fiber. -/
def zeroDerivativeCoefficientForcesFiberIdentity_claim27431 : Prop :=
  ∀ (F H : Type*) [Fintype F] [Field F] [Fintype H] [Group H]
    (_χ : H →* Fˣ) (multiplier : H → Fˣ) (h : H),
    multiplier 1 = 1 →
      (∀ k : H, multiplier (h * k) = multiplier k) →
        let fMultiplier : F × H → F × H := fun z =>
          ((multiplier z.2 : F) * z.1, z.2)
        ∀ x : F, fMultiplier (x, h) = (x, h)

end MathlibPlus.Open.ResearchFormalization.Claim27431
