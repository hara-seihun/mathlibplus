import Mathlib

namespace MathlibPlus.Analysis.Claim42833

/-- The dyadic shift multiplier on an exponential mode. -/
theorem dyadicFilter_multiplier_claim42833 (z y : ℂ) :
    Complex.exp (z * y) - (1 / Real.sqrt 2 : ℂ) *
        Complex.exp (z * (y - ((Real.log (2 : ℝ) : ℝ) : ℂ))) =
      (1 - (1 / Real.sqrt 2 : ℂ) *
        Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ))) *
        Complex.exp (z * y) := by
  rw [show z * (y - ((Real.log (2 : ℝ) : ℝ) : ℂ)) =
      z * y + (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) by ring]
  rw [Complex.exp_add]
  ring

/-- Every zero of the dyadic multiplier lies on the line `Re z = -1/2`. -/
theorem dyadicFilter_zero_re_claim42833 {z : ℂ}
    (hz : 1 - (1 / Real.sqrt 2 : ℂ) *
        Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) = 0) :
    z.re = -(1 / 2 : ℝ) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsqrt
  have hmul : (1 / (Real.sqrt 2 : ℂ)) *
      Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) = 1 := by
    exact sub_eq_zero.mp hz |>.symm
  have hexp : Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) =
      (Real.sqrt 2 : ℂ) := by
    calc
      Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) =
          (Real.sqrt 2 : ℂ) *
            ((1 / (Real.sqrt 2 : ℂ)) *
              Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ))) := by
                field_simp
      _ = (Real.sqrt 2 : ℂ) := by rw [hmul, mul_one]
  have hnorm : Real.exp (-z.re * Real.log (2 : ℝ)) = Real.sqrt 2 := by
    calc
      Real.exp (-z.re * Real.log (2 : ℝ)) =
          ‖Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ))‖ := by
            rw [Complex.norm_exp]
            congr 1
            rw [Complex.mul_re]
            simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
              Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
      _ = ‖(Real.sqrt 2 : ℂ)‖ := congrArg norm hexp
      _ = Real.sqrt 2 := by simp [abs_of_pos hsqrt]
  have hsqrt_exp : Real.sqrt 2 = Real.exp (Real.log (2 : ℝ) / 2) := by
    rw [← Real.exp_log hsqrt]
    rw [Real.log_sqrt (by norm_num)]
  rw [hsqrt_exp] at hnorm
  have heq : -z.re * Real.log (2 : ℝ) = Real.log (2 : ℝ) / 2 :=
    Real.exp_injective hnorm
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hprod : (z.re + 1 / 2) * Real.log (2 : ℝ) = 0 := by
    nlinarith [heq]
  have hsum : z.re + 1 / 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hlog)
  linarith

/-- The dyadic multiplier is nonzero on modes with positive real exponent. -/
theorem dyadicFilter_nonzero_of_re_pos_claim42833 {z : ℂ} (hz : 0 < z.re) :
    1 - (1 / Real.sqrt 2 : ℂ) *
        Complex.exp (-z * ((Real.log (2 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  have hline := dyadicFilter_zero_re_claim42833 hzero
  linarith

end MathlibPlus.Analysis.Claim42833
