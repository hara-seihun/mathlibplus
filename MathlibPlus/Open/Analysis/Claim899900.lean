import MathlibPlus.Open.Basic

namespace MathlibPlus.Open.Analysis.Claim899

/-- Yang's classical zero-free region with denominator 4.862, using the
literal decimal as Lean's exact rational decimal. -/
def classicalZeroFreeRegion : Prop :=
  ∀ (t σ : ℝ),
    2 ≤ t →
    1 - 1 / (4.862 * Real.log t) < σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.Analysis.Claim899

namespace MathlibPlus.Open.Analysis.Claim900

/-- The repaired BTY zero-free region with denominator 4.89566. -/
def repairedZeroFreeRegion : Prop :=
  ∀ (t σ : ℝ),
    3 ≤ t →
    1 - 1 / (4.89566 * Real.log t) < σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.Analysis.Claim900
