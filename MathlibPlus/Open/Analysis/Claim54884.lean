import Mathlib

namespace MathlibPlus.Open.Analysis.Claim54884

/-- Claim 54884: a real double zero of `H` is a zero of every first-order
projector `H + c H'`, for any complex coefficient. -/
def claim54884 : Prop :=
  ∀ (H : ℝ → ℂ) (c : ℂ) (x : ℝ),
    H x = 0 →
      deriv H x = 0 →
        H x + c * deriv H x = 0

end MathlibPlus.Open.Analysis.Claim54884
