import Mathlib

namespace MathlibPlus.Analysis

/-- An off-axis complex atom has the diagonal amplification from claim 7634.
The polar parametrization is not needed for the exact identity: nonzero real
and imaginary parts are the denominator and strictness conditions. -/
theorem claim7634_off_axis_diagonal_factor
    (A : ℂ) (hre : A.re ≠ 0) (him : A.im ≠ 0) :
    4 * A * (starRingEnd ℂ) A / (A + (starRingEnd ℂ) A) ^ 2 =
        ((Complex.normSq A / A.re ^ 2 : ℝ) : ℂ) ∧
      (1 : ℝ) < Complex.normSq A / A.re ^ 2 := by
  constructor
  · have hmul : A * (starRingEnd ℂ) A = (Complex.normSq A : ℂ) :=
      Complex.mul_conj A
    have hadd : A + (starRingEnd ℂ) A = (2 * A.re : ℂ) :=
      by simpa using Complex.add_conj A
    rw [show 4 * A * (starRingEnd ℂ) A = (4 : ℂ) *
        (A * (starRingEnd ℂ) A) by ring, hmul, hadd]
    rw [Complex.ofReal_div]
    have hden : (2 * (A.re : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (by exact_mod_cast hre)
    field_simp [hden]
    simp [Complex.ofReal_inv, pow_two, Complex.ofReal_mul]
    ring
  · rw [Complex.normSq_apply]
    have hre2 : 0 < A.re ^ 2 := sq_pos_of_ne_zero hre
    have him2 : 0 < A.im ^ 2 := sq_pos_of_ne_zero him
    exact (lt_div_iff₀ hre2).2 (by nlinarith)

end MathlibPlus.Analysis
