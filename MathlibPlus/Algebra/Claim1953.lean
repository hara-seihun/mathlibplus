import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

namespace MathlibPlus.Algebra

/--
Formalization of claim 1953: the displayed polynomial is pointwise positive
on the real line while its coefficient of `X` is negative.
-/
theorem claim1953 :
    (∀ b : ℝ, 0 < b ^ 2 - 8 * b + 64) ∧
      (Polynomial.X ^ 2 - 8 * Polynomial.X + (64 : Polynomial ℝ)).coeff 1 < 0 := by
  constructor
  · intro b
    nlinarith [sq_nonneg (b - 4)]
  · norm_num

end MathlibPlus.Algebra
