import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- Claim 1873: the polynomial `b^2 - b + 1` is positive on the real line,
while its linear coefficient is negative. -/
theorem claim1873_positivePolynomial (b : ℝ) :
    0 < b ^ 2 - b + 1 ∧
      Polynomial.coeff (Polynomial.X ^ 2 - Polynomial.X + 1 : Polynomial ℝ) 1 = -1 := by
  constructor
  · nlinarith [sq_nonneg (b - (1 / 2 : ℝ))]
  · rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_one]
    norm_num [Polynomial.coeff_X_one]

/-- The explicit rational function in Claim 7759 is bounded above by its
unique interior maximum on `[0,1]`. -/
theorem claim7759_ratio_max (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    72 * x * (1 - x) / (2 + x) ^ 2 ≤ 3 ∧
      (72 * x * (1 - x) / (2 + x) ^ 2 = 3 ↔ x = 2 / 5) := by
  have hden : 0 < (2 + x) ^ 2 := by
    positivity
  have hineq : 72 * x * (1 - x) ≤ 3 * (2 + x) ^ 2 := by
    nlinarith [sq_nonneg (5 * x - 2)]
  constructor
  · exact (div_le_iff₀ hden).2 hineq
  · constructor
    · intro heq
      have hcross : 72 * x * (1 - x) = 3 * (2 + x) ^ 2 := by
        exact (div_eq_iff (ne_of_gt hden)).mp heq
      have hsquare : (5 * x - 2) ^ 2 = 0 := by
        nlinarith
      nlinarith [sq_eq_zero_iff.mp hsquare]
    · intro hx
      rw [hx]
      norm_num

end MathlibPlus.Algebra
