import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.Claim1201

/-- The exact denominator and reciprocal-amplitude differences stated in claim
1201.  Decimal literals are exact rationals embedded in `ℝ`. -/
theorem exactDenominatorComparison :
    (51.331 : ℝ) - 51.323 = 1 / 125 ∧
      (1 / 51.323 : ℝ) - 1 / 51.331 = 8000 / 2634460913 ∧
      (51.34 : ℝ) - 51.323 = 17 / 1000 ∧
      (1 / 51.323 : ℝ) - 1 / 51.34 = 50 / 7749773 := by
  norm_num

end MathlibPlus.AnalyticNumberTheory.Claim1201
