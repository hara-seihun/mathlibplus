import Mathlib

namespace MathlibPlus.Analysis.BoundComparisons

/-- Claim 1513: the denominator `51.3401` gives a strictly larger closed
boundary than `51.34` at every real height `t ≥ 3`. -/
theorem closedVKInteriorization :
    (51.3401 : ℝ) - 51.34 = 1 / 10000 ∧
      0 < (1 / 10000 : ℝ) ∧
      ∀ t : ℝ, 3 ≤ t →
        1 - 1 / (51.34 * Real.log t) <
          1 - 1 / (51.3401 * Real.log t) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro t ht
    have ht_one : (1 : ℝ) < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos ht_one
    have hden_old : 0 < (51.34 : ℝ) * Real.log t := by positivity
    have hden_order :
        (51.34 : ℝ) * Real.log t < 51.3401 * Real.log t := by
      exact mul_lt_mul_of_pos_right (by norm_num) hlog
    have hinv :
        1 / (51.3401 * Real.log t) <
          1 / (51.34 * Real.log t) := by
      exact one_div_lt_one_div_of_lt hden_old hden_order
    linarith

end MathlibPlus.Analysis.BoundComparisons
