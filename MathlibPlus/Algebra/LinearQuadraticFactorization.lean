import Mathlib

namespace MathlibPlus.Algebra.LinearQuadraticFactorization

/-!
# Linear–quadratic binary factorization

The binary forms are represented by their dehomogenizations at `S = 1` in
`Polynomial R`.  The resultant is evaluated with the fixed form degrees `1` and
`2`, rather than inferred natural degrees, so the statement remains the binary
resultant identity when a leading coefficient vanishes.
-/

/-- The coefficient expansion of a linear form times a quadratic form. -/
theorem linearQuadraticProduct {R : Type*} [CommRing R]
    (a b c d e : R) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b) *
        (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X + Polynomial.C e) =
      Polynomial.C (a * c) * Polynomial.X ^ 3 +
        Polynomial.C (a * d + b * c) * Polynomial.X ^ 2 +
          Polynomial.C (a * e + b * d) * Polynomial.X + Polynomial.C (b * e) := by
  simp only [Polynomial.C_mul, map_add]
  ring

/-- The binary resultant of a linear form and a quadratic form. -/
theorem linearQuadraticResultant {R : Type*} [CommRing R]
    (a b c d e : R) :
    Polynomial.resultant
        (Polynomial.C a * Polynomial.X + Polynomial.C b)
        (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X + Polynomial.C e)
        1 2 =
      a ^ 2 * e - a * b * d + c * b ^ 2 := by
  simp [Polynomial.resultant, Polynomial.sylvester, Matrix.det_fin_three,
    Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X,
    Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Fin.addCases,
    Fin.natAdd]
  ring

end MathlibPlus.Algebra.LinearQuadraticFactorization
