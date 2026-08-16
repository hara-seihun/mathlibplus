import Mathlib

open scoped BigOperators ENNReal

namespace MathlibPlus.Open.Analysis

/-- At beta=3/5 and epsilon=1/10, continuation is negative while the
    corresponding positive uncut diagonal integral has value +infinity. -/
def explicitNegativeContinuedDiagonal_10328 : Prop :=
  let β : ℝ := 3 / 5
  let ε : ℝ := 1 / 10
  let continuedDiagonal : ℝ :=
    ε ^ 2 / (ε ^ 2 - (2 * β - 1) ^ 2)
  let uncutPositiveIntegral : ℝ≥0∞ :=
    ∫⁻ y : ℝ,
      ENNReal.ofReal ((ε / 2) * Real.exp (-ε * |y| + (2 * β - 1) * y))
  (¬ (|2 * β - 1| < ε)) ∧
    continuedDiagonal = -(1 / 3 : ℝ) ∧
    uncutPositiveIntegral = ∞ ∧
    ¬ (0 ≤ continuedDiagonal)

end MathlibPlus.Open.Analysis
