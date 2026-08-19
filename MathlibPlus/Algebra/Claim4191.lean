import Mathlib

namespace MathlibPlus.Algebra

/-- The symmetric Laplace numerator is the square of the difference. -/
theorem symmetricLaplaceNumerator_square_claim4191
    (common s q : ℝ) :
    common * (s ^ 2 + q ^ 2 - 2 * s * q) / 2 =
      common * (s - q) ^ 2 / 2 := by
  ring

end MathlibPlus.Algebra
