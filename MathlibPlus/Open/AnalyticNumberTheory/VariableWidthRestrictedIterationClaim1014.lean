import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Variable-width restricted iteration for the classical zeta zero-free region. -/
def variableWidthRestrictedIteration_claim1014 : Prop :=
  let A₀ : ℝ := 1 / 4.8594
  let H : ℝ := 3 * 10 ^ 12
  let ε : ℝ := 10 ^ (-100 : ℤ)
  ∀ A δ : ℝ,
    1 / 6 < A →
    A < A₀ →
    0 < δ →
    δ ≤ ε →
    A + δ ≤ A₀ →
    (∀ t : ℝ, H ≤ t →
      ∀ σ : ℝ,
        σ > 1 - A / Real.log t →
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
    ∀ t : ℝ, H ≤ t → t ≤ Real.exp 56.693 →
      ∀ σ : ℝ,
        σ > 1 - (A + δ) / Real.log t →
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
