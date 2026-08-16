import Mathlib

namespace MathlibPlus.Open.Analysis

def zeta_zero_free_region_4896 : Prop :=
  ∀ t σ : ℝ,
    3 ≤ t →
    σ > 1 - 1 / ((4.896 : ℝ) * Real.log t) →
    riemannZeta (σ + t * Complex.I) ≠ 0

end MathlibPlus.Open.Analysis
