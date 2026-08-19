import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact denominator and reciprocal-amplitude comparisons from admitted claim 1463. -/
def denominatorAndAmplitudeImprovements_claim1463 : Prop :=
  (4.8594 : ℝ) - 4.8568 = 13 / 5000 ∧
    (0 : ℝ) < 13 / 5000 ∧
    (1 / 4.8568 : ℝ) - 1 / 4.8594 = 1250 / 11346699 ∧
    (0 : ℝ) < 1250 / 11346699 ∧
    (4.862 : ℝ) - 4.8568 = 13 / 2500

end MathlibPlus.Open.Analysis
