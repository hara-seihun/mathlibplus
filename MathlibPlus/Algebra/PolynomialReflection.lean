import Mathlib

namespace MathlibPlus.Algebra.PolynomialReflection

/-- Claim 4943: replacing `X` by `-X` multiplies the degree-`d` coefficient
by `(-1)^d`. -/
theorem coeff_comp_neg_X {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ) :
    (P.comp (-Polynomial.X)).coeff d = (-1 : R) ^ d * P.coeff d := by
  rw [show (-Polynomial.X : Polynomial R) = Polynomial.C (-1) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  rw [mul_comm]

end MathlibPlus.Algebra.PolynomialReflection
