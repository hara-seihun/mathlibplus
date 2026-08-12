import Mathlib

namespace MathlibPlus.Analysis.Claim3107

/-- The sine and cosine values at a vertical half-period boundary of the
Dini factor.  The positive `L` hypothesis is the source context in which
`L = log(lambda)` is used. -/
theorem verticalHalfPeriod_sin (L : ℝ) (hL : 0 < L) (m : ℕ) (y : ℝ) :
    Complex.sin ((L : ℂ) * ((((m : ℝ) + 1 / 2) * Real.pi / L : ℝ) +
      (y : ℂ) * Complex.I)) =
      (((-1 : ℝ) ^ m : ℝ) : ℂ) * (Real.cosh (L * y) : ℂ) := by
  have sin_half_period :
      Real.sin (((m : ℝ) + 1 / 2) * Real.pi) = (-1 : ℝ) ^ m := by
    calc
      Real.sin (((m : ℝ) + 1 / 2) * Real.pi) =
          Real.sin ((m : ℝ) * Real.pi + Real.pi / 2) := by
            congr 1 <;> ring
      _ = (-1 : ℝ) ^ m := by
        rw [Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
          Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have cos_half_period :
      Real.cos (((m : ℝ) + 1 / 2) * Real.pi) = 0 := by
    calc
      Real.cos (((m : ℝ) + 1 / 2) * Real.pi) =
          Real.cos ((m : ℝ) * Real.pi + Real.pi / 2) := by
            congr 1 <;> ring
      _ = 0 := by
        rw [Real.cos_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
          Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have half_period_argument :
      (L : ℂ) * ((((m : ℝ) + 1 / 2) * Real.pi / L : ℝ) +
        (y : ℂ) * Complex.I) =
        ((((m : ℝ) + 1 / 2) * Real.pi : ℝ) : ℂ) +
          ((L * y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num <;> field_simp <;> ring
  rw [half_period_argument, Complex.sin_add_mul_I]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, sin_half_period,
    cos_half_period, ← Complex.ofReal_cosh]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The cosine value at a vertical half-period boundary of the Dini factor. -/
theorem verticalHalfPeriod_cos (L : ℝ) (hL : 0 < L) (m : ℕ) (y : ℝ) :
    Complex.cos ((L : ℂ) * ((((m : ℝ) + 1 / 2) * Real.pi / L : ℝ) +
      (y : ℂ) * Complex.I)) =
      -Complex.I * (((-1 : ℝ) ^ m : ℝ) : ℂ) *
        (Real.sinh (L * y) : ℂ) := by
  have sin_half_period :
      Real.sin (((m : ℝ) + 1 / 2) * Real.pi) = (-1 : ℝ) ^ m := by
    calc
      Real.sin (((m : ℝ) + 1 / 2) * Real.pi) =
          Real.sin ((m : ℝ) * Real.pi + Real.pi / 2) := by
            congr 1 <;> ring
      _ = (-1 : ℝ) ^ m := by
        rw [Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
          Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have cos_half_period :
      Real.cos (((m : ℝ) + 1 / 2) * Real.pi) = 0 := by
    calc
      Real.cos (((m : ℝ) + 1 / 2) * Real.pi) =
          Real.cos ((m : ℝ) * Real.pi + Real.pi / 2) := by
            congr 1 <;> ring
      _ = 0 := by
        rw [Real.cos_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
          Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have half_period_argument :
      (L : ℂ) * ((((m : ℝ) + 1 / 2) * Real.pi / L : ℝ) +
        (y : ℂ) * Complex.I) =
        ((((m : ℝ) + 1 / 2) * Real.pi : ℝ) : ℂ) +
          ((L * y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num <;> field_simp <;> ring
  rw [half_period_argument, Complex.cos_add_mul_I]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, sin_half_period,
    cos_half_period, ← Complex.ofReal_sinh]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The numerator of the Dini factor has magnitude at least
`b_m cosh (L*y)` on a vertical half-period boundary. -/
theorem verticalHalfPeriod_numerator_bound
    (L : ℝ) (hL : 0 < L) (m : ℕ) (y : ℝ) :
    let b : ℝ := ((m : ℝ) + 1 / 2) * Real.pi / L
    let z : ℂ := (b : ℂ) + (y : ℂ) * Complex.I
    b * Real.cosh (L * y) ≤
      ‖z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) *
        Complex.cos ((L : ℂ) * z)‖ := by
  let b : ℝ := ((m : ℝ) + 1 / 2) * Real.pi / L
  let z : ℂ := (b : ℂ) + (y : ℂ) * Complex.I
  change b * Real.cosh (L * y) ≤
    ‖z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) *
      Complex.cos ((L : ℂ) * z)‖
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsin : Complex.sin ((L : ℂ) * z) =
      (((-1 : ℝ) ^ m : ℝ) : ℂ) * (Real.cosh (L * y) : ℂ) := by
    dsimp [z, b]
    exact verticalHalfPeriod_sin L hL m y
  have hcos : Complex.cos ((L : ℂ) * z) =
      -Complex.I * (((-1 : ℝ) ^ m : ℝ) : ℂ) *
        (Real.sinh (L * y) : ℂ) := by
    dsimp [z, b]
    exact verticalHalfPeriod_cos L hL m y
  have hre :
      (z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) *
        Complex.cos ((L : ℂ) * z)).re =
      ((-1 : ℝ) ^ m) * b * Real.cosh (L * y) := by
    rw [hsin, hcos]
    simp only [z, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.div_re,
      Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im, zero_mul, mul_zero,
      sub_zero, zero_sub, neg_zero, one_mul, mul_one]
    norm_num
    ring
  calc
    b * Real.cosh (L * y) =
        |(((-1 : ℝ) ^ m) * b * Real.cosh (L * y))| := by
      rw [abs_mul, abs_mul, abs_pow]
      norm_num
      rw [abs_of_nonneg hb, abs_of_nonneg (Real.cosh_pos _).le]
    _ = |(z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) *
        Complex.cos ((L : ℂ) * z)).re| := by rw [hre]
    _ ≤ ‖z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) *
        Complex.cos ((L : ℂ) * z)‖ := Complex.abs_re_le_norm _

end MathlibPlus.Analysis.Claim3107
