import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 9609: multiplication by the high-order Gripfall factor leaves every
coefficient below degree `4 * m` unchanged. -/
theorem highOrderGripfallFactor_preservesCoeff
    (P : Polynomial ℤ) (m d : ℕ) (hd : d < 4 * m) :
    (P * (1 + Polynomial.X ^ (4 * m))).coeff d = P.coeff d := by
  rw [mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  simp [not_le_of_gt hd]

end MathlibPlus.Algebra
