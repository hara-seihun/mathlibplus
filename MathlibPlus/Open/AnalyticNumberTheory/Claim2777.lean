import MathlibPlus.Basic

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Claim 2777: the stated denominator-4.80 zero-free region for the Riemann zeta
function.  The decimal is Lean's exact real decimal. -/
def globalZetaZeroFreeDenominator480_claim2777 : Prop :=
  ∀ (t σ : ℝ), 2 ≤ t →
    1 - 1 / ((4.80 : ℝ) * Real.log t) < σ →
      riemannZeta (σ + t * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
