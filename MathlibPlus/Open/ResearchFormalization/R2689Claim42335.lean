import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2689Claim42335

/-- Claim 42335: the integer tangent bound has the exact square remainder. -/
def claim42335 : Prop :=
  ∀ k r : ℤ,
    k * (k - 1) ≥ (2 * r - 1) * k - r ^ 2 ∧
      k * (k - 1) - ((2 * r - 1) * k - r ^ 2) = (k - r) ^ 2

end MathlibPlus.Open.ResearchFormalization.R2689Claim42335
