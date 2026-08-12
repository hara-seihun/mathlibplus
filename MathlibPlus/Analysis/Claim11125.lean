import Mathlib

namespace MathlibPlus.Analysis.Claim11125

/-- The quadratic factor in the shell-birth kernel is positive everywhere. -/
theorem quadraticFactor_positive (x : ℝ) :
    0 < 7 * x ^ 2 - 576 * x + 20160 := by
  have hdisc : (576 : ℝ) ^ 2 - 4 * 7 * 20160 < 0 := by norm_num
  nlinarith [sq_nonneg (7 * x - 288)]

/-- The displayed quadratic shell-birth kernel is strictly negative on the
positive half-line. -/
theorem quadraticShellBirthKernel_negative {x : ℝ} (hx : 0 < x) :
    -x ^ 2 * (7 * x ^ 2 - 576 * x + 20160) / 23040 < 0 := by
  have hquad : 0 < 7 * x ^ 2 - 576 * x + 20160 := quadraticFactor_positive x
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hnum : -x ^ 2 * (7 * x ^ 2 - 576 * x + 20160) < 0 := by
    nlinarith [mul_pos hx2 hquad]
  have hden : (0 : ℝ) < 23040 := by norm_num
  exact div_neg_of_neg_of_pos hnum hden

end MathlibPlus.Analysis.Claim11125
