import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Claim 1009: the repaired global denominator `4.8594` gives the stated
classical Riemann-zeta zero-free region above height two. -/
def globalZetaZeroFreeRegionDenominator48594_claim1009 : Prop :=
  ∀ (t σ : ℝ),
    2 ≤ t →
      σ > 1 - 1 / ((48594 / 10000 : ℝ) * Real.log t) →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
