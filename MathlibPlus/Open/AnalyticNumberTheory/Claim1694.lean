import MathlibPlus.Basic

namespace MathlibPlus.Open.AnalyticNumberTheory

noncomputable section

/-- The normalized Riemann-zeta bound from admitted claim 1694. -/
def bastienRogalskiNormalizedZetaBound_claim1694 : Prop :=
  ∀ s : ℝ, 1 < s →
    (s - 1) * (riemannZeta (s : ℂ)).re < Real.rpow 2 (s - 1)

end

end MathlibPlus.Open.AnalyticNumberTheory
