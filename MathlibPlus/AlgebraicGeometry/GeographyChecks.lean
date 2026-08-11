import Mathlib

namespace MathlibPlus.AlgebraicGeometry

/-- Claim 14670: the displayed numerical pair passes exactly the four
positivity/geography inequalities supplied by the source. The arithmetic is
recorded over `ℤ`; no geometric existence assertion is added. -/
theorem claim14670_numericalAdmissibilityChecks :
    (0 : ℤ) < 11 ∧
      (0 : ℤ) < 13 ∧
      (5 : ℤ) * 11 ≥ 13 - 36 ∧
      (11 : ℤ) ≤ 3 * 13 := by
  norm_num

end MathlibPlus.AlgebraicGeometry
