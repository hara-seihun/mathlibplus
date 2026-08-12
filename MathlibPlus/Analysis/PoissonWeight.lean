import Mathlib.Probability.Distributions.Poisson.Basic

namespace MathlibPlus.Analysis

/-- Claim 4223: the real mass of the Poisson measure at `n` is the displayed
Poisson weight for a positive real parameter. -/
theorem poisson_weight_formula_claim4223 {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (ProbabilityTheory.poissonMeasure x.toNNReal).real {n} =
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) := by
  rw [ProbabilityTheory.poissonMeasure_real_singleton,
    Real.coe_toNNReal x hx.le]

end MathlibPlus.Analysis
