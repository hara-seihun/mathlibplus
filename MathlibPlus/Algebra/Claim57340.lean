import Mathlib

namespace MathlibPlus.Algebra

/-- The explicit polynomial factorization in claim 57340. -/
theorem claim57340_polynomial_factorization :
    let L : Polynomial ℤ :=
      Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
        Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1
    let H : Polynomial ℤ := L + Polynomial.X ^ 5
    H = (Polynomial.X - 1) ^ 2 * (Polynomial.X + 1) ^ 2 *
      (Polynomial.X ^ 2 + Polynomial.X + 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.X + 1) := by
  dsimp
  ring

end MathlibPlus.Algebra
