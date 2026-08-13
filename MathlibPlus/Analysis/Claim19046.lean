import Mathlib

namespace MathlibPlus.Analysis.Claim19046

/-- A real quadratic with negative leading coefficient, negative value at zero,
and negative discriminant is strictly negative everywhere. -/
theorem negativeQuadratic_of_negative_leading_coefficient
    (a b c x : ℝ) (ha : a < 0) (_hc : c < 0)
    (hdisc : b ^ 2 - 4 * a * c < 0) :
    a * x ^ 2 + b * x + c < 0 := by
  have hs : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
  have hprod : 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
    nlinarith
  have h4a : 4 * a < 0 := by nlinarith
  by_contra hq
  have hq0 : 0 ≤ a * x ^ 2 + b * x + c := le_of_not_gt hq
  have hnonpos : 4 * a * (a * x ^ 2 + b * x + c) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt h4a) hq0
  exact (not_lt_of_ge hnonpos) hprod

end MathlibPlus.Analysis.Claim19046
