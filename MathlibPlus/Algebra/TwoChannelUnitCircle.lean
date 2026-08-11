import Mathlib.Tactic

namespace MathlibPlus.Algebra.TwoChannelUnitCircle

/-- Claim 15635: two unit vectors satisfy the sharp two-channel lower bound. -/
theorem sharpTwoChannelUnitCircleLowerBound
    (u v c s : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    1 - |c| ≤ u ^ 2 + (u * c - v * s) ^ 2 := by
  have hAB :
      (u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2 = 1 := by
    calc
      (u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2 =
          (u ^ 2 + v ^ 2) ^ 2 := by ring
      _ = 1 := by rw [huv]; norm_num
  have hrot :
      (c * (u ^ 2 - v ^ 2) - s * (2 * u * v)) ^ 2 +
          (s * (u ^ 2 - v ^ 2) + c * (2 * u * v)) ^ 2 = 1 := by
    calc
      (c * (u ^ 2 - v ^ 2) - s * (2 * u * v)) ^ 2 +
          (s * (u ^ 2 - v ^ 2) + c * (2 * u * v)) ^ 2 =
          (c ^ 2 + s ^ 2) *
            ((u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2) := by ring
      _ = 1 := by rw [hcs, hAB]; norm_num
  have hq_lower :
      -1 ≤ c * (u ^ 2 - v ^ 2) - s * (2 * u * v) := by
    nlinarith [sq_nonneg (s * (u ^ 2 - v ^ 2) + c * (2 * u * v))]
  have hq_upper :
      c * (u ^ 2 - v ^ 2) - s * (2 * u * v) ≤ 1 := by
    nlinarith [sq_nonneg (s * (u ^ 2 - v ^ 2) + c * (2 * u * v))]
  have hdiff :
      (u * c - v * s) ^ 2 - v ^ 2 =
        c * (c * (u ^ 2 - v ^ 2) - 2 * u * v * s) := by
    calc
      (u * c - v * s) ^ 2 - v ^ 2 =
          c ^ 2 * (u ^ 2 - v ^ 2) - 2 * u * v * c * s +
            v ^ 2 * (c ^ 2 + s ^ 2 - 1) := by ring
      _ = c * (c * (u ^ 2 - v ^ 2) - 2 * u * v * s) := by
        rw [hcs]
        ring
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    have hnonneg :
        0 ≤ c * (1 + (c * (u ^ 2 - v ^ 2) - s * (2 * u * v))) := by
      apply mul_nonneg hc
      linarith
    nlinarith [hnonneg, hdiff, huv]
  · have hcneg : c < 0 := lt_of_not_ge hc
    rw [abs_of_neg hcneg]
    have hnonneg :
        0 ≤ (-c) * (1 - (c * (u ^ 2 - v ^ 2) - s * (2 * u * v))) := by
      apply mul_nonneg (by linarith)
      linarith
    nlinarith [hnonneg, hdiff, huv]

end MathlibPlus.Algebra.TwoChannelUnitCircle
