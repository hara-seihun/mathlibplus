import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MathlibPlus.Open.NumberTheory

/-- Claim 1719: the published denominator `4.862` zero-free region, with the
real height and real abscissa made explicit and the argument of zeta embedded in
`Complex`.  The decimal is represented exactly as `4862 / 1000`. -/
def publishedDenominator_claim1719 : Prop :=
  ∀ (t σ : ℝ),
    2 ≤ t →
    1 - 1 / ((4862 : ℝ) / 1000 * Real.log t) < σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.NumberTheory
