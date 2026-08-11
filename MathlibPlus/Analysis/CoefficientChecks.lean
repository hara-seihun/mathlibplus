import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 902: the exact coefficient decrease and its strict ordering. -/
theorem exactCoefficientDecrease_4896_489566 :
    (4.896 : ℝ) - 4.89566 = 17 / 50000 ∧
      (17 / 50000 : ℝ) = 0.00034 ∧
      (4.89566 : ℝ) < 4.896 := by
  norm_num

/-- Claim 904: the displayed test polynomial is positive on the unit interval,
with the two endpoint values recorded explicitly. -/
theorem testFunctionPolynomial_positive_on_unit_interval :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      0 < 1 - (851 / 859) * x + (780 / 859) * x ^ 2 -
        (525 / 859) * x ^ 3 + (171 / 859) * x ^ 4 +
        (28 / 859) * x ^ 5 - (29 / 859) * x ^ 6) ∧
      (1 - (851 / 859) * (0 : ℝ) + (780 / 859) * 0 ^ 2 -
        (525 / 859) * 0 ^ 3 + (171 / 859) * 0 ^ 4 +
        (28 / 859) * 0 ^ 5 - (29 / 859) * 0 ^ 6 = 1) ∧
      (1 - (851 / 859) * (1 : ℝ) + (780 / 859) * 1 ^ 2 -
        (525 / 859) * 1 ^ 3 + (171 / 859) * 1 ^ 4 +
        (28 / 859) * 1 ^ 5 - (29 / 859) * 1 ^ 6 = 433 / 859) := by
  have hpos : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      0 < 859 - 851 * x + 780 * x ^ 2 - 525 * x ^ 3 +
        171 * x ^ 4 + 28 * x ^ 5 - 29 * x ^ 6 := by
    intro x hx0 hx1
    have hdecomp :
        859 - 851 * x + 780 * x ^ 2 - 525 * x ^ 3 +
            171 * x ^ 4 + 28 * x ^ 5 - 29 * x ^ 6 =
          859 * (1 - x) ^ 6 +
            4303 * x * (1 - x) ^ 5 +
            9410 * x ^ 2 * (1 - x) ^ 4 +
            11265 * x ^ 3 * (1 - x) ^ 3 +
            7651 * x ^ 4 * (1 - x) ^ 2 +
            2814 * x ^ 5 * (1 - x) +
            433 * x ^ 6 := by ring
    rw [hdecomp]
    rcases lt_or_eq_of_le hx1 with hx1lt | rfl
    · have h1 : 0 < 859 * (1 - x) ^ 6 := by positivity
      have hrest : 0 ≤
          4303 * x * (1 - x) ^ 5 +
            9410 * x ^ 2 * (1 - x) ^ 4 +
            11265 * x ^ 3 * (1 - x) ^ 3 +
            7651 * x ^ 4 * (1 - x) ^ 2 +
            2814 * x ^ 5 * (1 - x) +
            433 * x ^ 6 := by positivity
      nlinarith
    · norm_num
  constructor
  · intro x hx0 hx1
    have hx := hpos x hx0 hx1
    norm_num at hx ⊢
    nlinarith
  constructor <;> norm_num

end MathlibPlus.Analysis
