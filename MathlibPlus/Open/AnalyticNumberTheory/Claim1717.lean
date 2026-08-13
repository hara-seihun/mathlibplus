import MathlibPlus.Basic

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Faithful registry formalization of admitted claim 1717. -/
def globalClassicalZetaZeroFreeDenominator483_claim1717 : Prop :=
  ∀ (t σ : ℝ), 2 ≤ t →
    1 - 1 / ((4.83 : ℝ) * Real.log t) < σ →
      riemannZeta (σ + t * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
