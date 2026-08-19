import MathlibPlus.Open.ResearchFormalizationR4542

namespace MathlibPlus.Open.ResearchFormalization.R2958Claim45554

open MathlibPlus.Open.R4542

noncomputable section

/-- R-2958.1: the central and one-step marker maps on every homogeneous
residual-weight monomial. -/
def centralAndOneStepMarkerMaps_claim45554 : Prop :=
  ∀ (W r : ℕ) (part : Partition),
    sourceMonomialWeight r part = W →
      (∀ s : ℕ, 1 ≤ s →
        Phi s (sourceMonomial r part) = targetMonomial (r + s) part) ∧
        Phi 2 (sourceMonomial r part) = targetMonomial (r + 2) part ∧
          Phi 1 (sourceMonomial r part) = targetMonomial (r + 1) part

end

end MathlibPlus.Open.ResearchFormalization.R2958Claim45554
