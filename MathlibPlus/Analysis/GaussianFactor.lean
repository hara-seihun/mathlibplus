import Mathlib

namespace MathlibPlus.Analysis

/-- The real Gaussian factor is positive, and multiplying by it does not
create or remove real zeros.  The source's undefined ``cosine product`` is
represented here by the arbitrary real cofactor `c`. -/
theorem gaussianFactor_nonvanishing (σ t c : ℝ) :
    0 < Real.exp (-(σ ^ 2 * t ^ 2) / 2) ∧
      (Real.exp (-(σ ^ 2 * t ^ 2) / 2) * c = 0 ↔ c = 0) := by
  have hpos : 0 < Real.exp (-(σ ^ 2 * t ^ 2) / 2) := by
    positivity
  constructor
  · exact hpos
  · rw [mul_eq_zero]
    simp [ne_of_gt hpos]

end MathlibPlus.Analysis
