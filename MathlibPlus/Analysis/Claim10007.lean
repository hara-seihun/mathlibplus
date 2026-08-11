import Mathlib

namespace MathlibPlus.Analysis.Claim10007

/-- Exact first/second dyadic coefficient arithmetic from the packet. -/
theorem exactFirstSecondDyadicCoefficient_claim10007 :
    (1 : ℝ) * Real.log 2 = Real.log 2 ∧
    (4 * Real.sqrt 2 + (1 : ℝ) / 6) * Real.log 2 ≠ Real.log 2 := by
  constructor
  · ring
  · have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      have h : (0 : ℝ) ≤ 2 := by norm_num
      simpa using Real.sq_sqrt h
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith

end MathlibPlus.Analysis.Claim10007
