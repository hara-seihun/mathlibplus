import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0251Claim14999

/-- Claim 14999: the exact hyperbolic reparameterization on `0 < A < B`. -/
def hyperbolicParameterIdentity_claim14999 : Prop :=
  ∀ (A B : ℝ),
    0 < A →
    A < B →
    Real.arcosh ((A ^ 2 + B ^ 2) / (B ^ 2 - A ^ 2)) =
      2 * Real.artanh (A / B)

end MathlibPlus.Open.ResearchFormalization.RO0251Claim14999
