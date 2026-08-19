import Mathlib

namespace MathlibPlus.Algebra.Claim4197

/-- The radial-average bound for two complex mode rates. -/
theorem pairRateBound
    (b c : ℂ) (R_b R_c : ℝ)
    (hb : 2 * b.re + ‖b‖ ^ 2 = R_b ^ 2 - 1)
    (hc : 2 * c.re + ‖c‖ ^ 2 = R_c ^ 2 - 1) :
    b.re + c.re + ‖b * c‖ ≤
      ((R_b ^ 2 - 1) + (R_c ^ 2 - 1)) / 2 := by
  have hnorm_b : 0 ≤ ‖b‖ := norm_nonneg b
  have hnorm_c : 0 ≤ ‖c‖ := norm_nonneg c
  have hprod : ‖b * c‖ = ‖b‖ * ‖c‖ := norm_mul b c
  have hamgm : 2 * (‖b‖ * ‖c‖) ≤ ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - ‖c‖)]
  rw [hprod]
  nlinarith

end MathlibPlus.Algebra.Claim4197
