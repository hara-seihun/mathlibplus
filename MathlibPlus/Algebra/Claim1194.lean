import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

namespace MathlibPlus.Algebra

/--
Formalization of claim 1194: pointwise positivity of `b^2-b+1` does not
prevent a negative coefficient, and the displayed product retains one.
-/
theorem claim1194 :
    (∀ b : ℝ, 0 < b ^ 2 - b + 1) ∧
      (Polynomial.X ^ 2 - Polynomial.X + (1 : Polynomial ℝ)).coeff 1 < 0 ∧
      (Polynomial.X * (Polynomial.X ^ 2 - Polynomial.X + (1 : Polynomial ℝ))).coeff 2 < 0 := by
  constructor
  · intro b
    nlinarith [sq_nonneg (b - (1 / 2 : ℝ))]
  · constructor
    · have h :
          (Polynomial.X ^ 2 - Polynomial.X + (1 : Polynomial ℝ)).coeff 1 = -1 := by
        simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_one]
      rw [h]
      norm_num
    · rw [Polynomial.coeff_X_mul]
      simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one]

end MathlibPlus.Algebra
