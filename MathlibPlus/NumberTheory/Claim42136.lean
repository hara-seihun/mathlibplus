import Mathlib
namespace MathlibPlus.NumberTheory
/-- The explicit integer polynomial used in the Lehmer interlacing fixture. -/
noncomputable def lehmerInterlacingPolynomial_claim42136 : Polynomial ℤ :=
  Polynomial.X ^ 11 - 2 * Polynomial.X ^ 9 - 4 * Polynomial.X ^ 8 -
    4 * Polynomial.X ^ 7 - 3 * Polynomial.X ^ 6 - Polynomial.X ^ 5 +
    Polynomial.X ^ 4 + 3 * Polynomial.X ^ 3 + 4 * Polynomial.X ^ 2 +
    3 * Polynomial.X + 1
end MathlibPlus.NumberTheory
