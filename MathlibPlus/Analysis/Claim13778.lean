import Mathlib

namespace MathlibPlus.Analysis

/-- The two explicit phases in admitted claim 13778 have opposite signs for
    the source's generic dyadic leading-coefficient factor
    `1 / 2 - cos (2 * x * log 2)`. -/
theorem claim13778_genericLeadingCoefficientSigns :
    let xMinus : ℝ := Real.pi / (12 * Real.log 2)
    let xPlus : ℝ := Real.pi / (2 * Real.log 2)
    (1 / 2 - Real.cos (2 * xMinus * Real.log 2) < 0) ∧
      (0 < 1 / 2 - Real.cos (2 * xPlus * Real.log 2)) := by
  dsimp
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (ne_of_gt (Real.log_pos (by norm_num)))
  have hminus :
      2 * (Real.pi / (12 * Real.log 2)) * Real.log 2 = Real.pi / 6 := by
    field_simp
    ring
  have hplus :
      2 * (Real.pi / (2 * Real.log 2)) * Real.log 2 = Real.pi := by
    field_simp
  constructor
  · rw [hminus, Real.cos_pi_div_six]
    have hsqrt : (1 : ℝ) < Real.sqrt 3 := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
      have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        norm_num
      nlinarith
    nlinarith
  · rw [hplus, Real.cos_pi]
    norm_num

end MathlibPlus.Analysis
