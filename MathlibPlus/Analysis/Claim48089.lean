import Mathlib

/-!
# Analytic Mellin zero off the critical line (claim 48089)

This file records the exact finite-factor calculation.  It does not assert a
statement about the Riemann zeta function.
-/

namespace MathlibPlus.Analysis.Claim48089

noncomputable def alpha : ℝ := Real.log (2 + Real.sqrt 3)

noncomputable def z0 : ℂ :=
  ((alpha : ℂ) + (Real.pi : ℂ) * Complex.I) / (Real.log 2 : ℂ)

noncomputable def mellinValue (z : ℂ) : ℂ :=
  2 + Complex.cosh (z * (Real.log 2 : ℂ))

noncomputable def rho0 : ℂ := (1 / 2 : ℂ) + z0

theorem alpha_pos : 0 < alpha := by
  dsimp [alpha]
  apply Real.log_pos
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  nlinarith

theorem cosh_alpha : Real.cosh alpha = 2 := by
  have hx : 0 < 2 + Real.sqrt (3 : ℝ) := by positivity
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  rw [alpha, Real.cosh_log hx]
  field_simp
  nlinarith

theorem mellinValue_at_z0 : mellinValue z0 = 0 := by
  have hlog2 : (Real.log (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have hzmul : z0 * (Real.log 2 : ℂ) =
      (alpha : ℂ) + (Real.pi : ℂ) * Complex.I := by
    dsimp [z0]
    field_simp [hlog2]
  have hcosh : Complex.cosh (alpha : ℂ) = 2 := by
    exact_mod_cast cosh_alpha
  have hc : Complex.cosh ((Real.pi : ℂ) * Complex.I) = -1 := by
    rw [Complex.cosh_mul_I]
    simp
  have hs : Complex.sinh ((Real.pi : ℂ) * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]
    simp
  rw [mellinValue, hzmul, Complex.cosh_add, hcosh, hc, hs]
  ring

theorem z0_re_pos : 0 < z0.re := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [z0, Complex.div_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, sub_zero, Complex.normSq_apply]
  have ha : 0 < alpha := alpha_pos
  field_simp
  norm_num
  exact mul_pos ha hlog2

theorem rho0_re_gt_half : (1 / 2 : ℝ) < rho0.re := by
  dsimp [rho0]
  simpa using (add_lt_add_left z0_re_pos (1 / 2 : ℝ))

end MathlibPlus.Analysis.Claim48089
