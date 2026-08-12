import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Claim 1069: Yang's global zero-free region with denominator 51.34. -/
def yangGlobalZeroFreeRegion_claim1069 : Prop :=
  ∀ (σ t : ℝ),
    3 ≤ t →
    σ > 1 - 1 /
      ((2567 / 50 : ℝ) * Real.rpow (Real.log t) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ)) →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
