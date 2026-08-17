import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198Claim32118

noncomputable section

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

/-- Claim 32118: the normalized quotient-identity affine prime-fibre
permutation has the exact fibrewise multiplier/translation form. -/
def normalizedAffinePrimeFibrePermutation_claim32118 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H],
    elementarySylowP p H →
      ∀ (f : (H × ZMod p) ≃ (H × ZMod p)),
        normalizedQuotientIdentityAffine f →
          ∃ lambda : H → (ZMod p)ˣ, ∃ s : H → ZMod p,
            normalizedAffineProfile f lambda s

end

end MathlibPlus.Open.ResearchFormalization.R1198Claim32118
