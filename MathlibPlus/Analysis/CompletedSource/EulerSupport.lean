import Mathlib

namespace MathlibPlus.Analysis.CompletedSource

/-- The exact rational endpoint `α₊ = 0.138806` and `ρ = 1/2` give the
strict decay exponent recorded in admitted claim 327. -/
theorem certifiedEulerDecayExponent :
    ((1 / 3 : ℝ) - 2 * (138806 / 1000000 : ℝ)) * Real.log 2 >
      (386230850970 / 10000000000000 : ℝ) := by
  have t : |(2⁻¹ : ℝ)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le
    (show |(2⁻¹ : ℝ)| < 1 by rw [t]; norm_num) 50
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : ℝ), Real.log_inv, ← sub_eq_add_neg] at z
  have hlow := (abs_sub_le_iff.mp z).1
  norm_num at hlow ⊢
  nlinarith

end MathlibPlus.Analysis.CompletedSource
