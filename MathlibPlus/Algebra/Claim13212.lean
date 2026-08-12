import Mathlib

namespace MathlibPlus.Algebra.Claim13212

/-- A nonzero integral resultant has absolute value at least one. -/
theorem resultant_abs_ge_one {Q A : Polynomial ℤ}
    (h : Polynomial.resultant Q A ≠ 0) :
    (1 : ℤ) ≤ |Polynomial.resultant Q A| := by
  exact Int.one_le_abs h

/-- The logarithm of the absolute value of a nonzero integral resultant is
nonnegative.  The cast to `ℝ` is made explicit because the source's logarithm
is real-valued. -/
theorem resultant_log_nonneg {Q A : Polynomial ℤ}
    (h : Polynomial.resultant Q A ≠ 0) :
    0 ≤ Real.log |((Polynomial.resultant Q A : ℤ) : ℝ)| := by
  have hcast : ((Polynomial.resultant Q A : ℤ) : ℝ) ≠ 0 :=
    (Int.cast_ne_zero.mpr h)
  have habs : (1 : ℝ) ≤ |((Polynomial.resultant Q A : ℤ) : ℝ)| := by
    exact_mod_cast (resultant_abs_ge_one h)
  exact Real.log_nonneg habs

end MathlibPlus.Algebra.Claim13212
