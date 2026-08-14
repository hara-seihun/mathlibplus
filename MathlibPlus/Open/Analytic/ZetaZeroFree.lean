import Mathlib

namespace MathlibPlus.Open.Analytic

noncomputable section

def claim1619 : Prop :=
  ∀ (σ t : ℝ), 2 ≤ t →
    1 - 1 / ((4.852 : ℝ) * Real.log t) < σ →
    riemannZeta (σ + t * Complex.I) ≠ 0

end
end MathlibPlus.Open.Analytic
