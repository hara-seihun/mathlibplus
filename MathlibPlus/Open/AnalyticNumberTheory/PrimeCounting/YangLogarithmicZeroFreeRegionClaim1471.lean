import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Yang's logarithmic zero-free region from admitted claim 1471. -/
def yangLogarithmicZeroFreeRegion_claim1471 : Prop :=
  ∀ (t σ : ℝ),
    3 ≤ t →
    σ > 1 - Real.log (Real.log t) / ((19.62 : ℝ) * Real.log t) →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
