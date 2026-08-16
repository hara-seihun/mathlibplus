import Mathlib

/-!
# Cup-positivity obstructions

A general polynomial witness extracted from source record `C-0079`.  It records
exactly why pointwise positivity cannot by itself establish coefficientwise
positivity of the packet's cup-coordinate polynomials.
-/

namespace MathlibPlus.CupPositivity

/-- The polynomial `b² - b + 1` is strictly positive at every real point but has
negative linear coefficient. -/
theorem pointwisePositiveNotCoeffwise :
    (∀ b : ℝ, 0 < b ^ 2 - b + 1) ∧
      (Polynomial.X ^ 2 - Polynomial.X + 1 : Polynomial ℤ).coeff 1 < 0 := by
  constructor
  · intro b
    nlinarith [sq_nonneg (2 * b - 1)]
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

end MathlibPlus.CupPositivity
