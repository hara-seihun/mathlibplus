import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0537Claim29449

/-- Claim 29449: the squarefree two-root interpolation trade is the exact
ambient rational identity, independently of any realized tree collision. -/
def squarefreeInterpolationIdentity_claim29449 : Prop :=
  ∀ {K : Type*} [Field K] (Y kappa₁ kappa₂ : K),
    kappa₁ ≠ kappa₂ →
      (Y + kappa₂) / (kappa₂ - kappa₁) -
          (Y + kappa₁) / (kappa₂ - kappa₁) = 1

end MathlibPlus.Open.ResearchFormalization.R0537Claim29449
