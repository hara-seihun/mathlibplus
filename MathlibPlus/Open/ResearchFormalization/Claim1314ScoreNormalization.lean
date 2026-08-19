import MathlibPlus.Open.Research.CertifiedCellMargins

namespace MathlibPlus.Open.ResearchFormalization.Claim1314

noncomputable section

open MathlibPlus.Open.Research

/-- The denominator from Claim 1313, with its coefficient and argument
explicit. -/
def axlerDenominator (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

/-- Claim 1314: on the packet's positive-coefficient, real-log domain, the
strict denominator inequality is equivalent to the score inequality; the
same domain carries the displayed derivative and persistence of positivity
from a starting point along its half-line. -/
def claim_1314 : Prop :=
  (∀ (c x : ℝ),
    0 < c →
    1 < x →
      (0 < axlerDenominator c x →
        (primeCountingReal x < x / axlerDenominator c x ↔ B x < c)) ∧
      HasDerivAt (fun y : ℝ => axlerDenominator c y)
        ((1 + c / (Real.log x) ^ 2) / x) x) ∧
  (∀ (c x : ℝ),
    0 < c →
    1 < x →
      0 < (1 + c / (Real.log x) ^ 2) / x) ∧
  (∀ (c x₀ : ℝ),
    0 < c →
    1 < x₀ →
    0 < axlerDenominator c x₀ →
      ∀ x : ℝ, x₀ ≤ x → 0 < axlerDenominator c x)

end

end MathlibPlus.Open.ResearchFormalization.Claim1314
