import Mathlib

/-!
# Degree-seven trace polynomial

The displayed polynomial in admitted claim 13230 is recorded as a polynomial
with integer coefficients.  The claim gives no ambient evaluation domain.
-/

namespace MathlibPlus.Algebra.Claim13230

/-- The degree-seven trace polynomial from claim 13230. -/
noncomputable def degreeSevenTracePolynomial : Polynomial ℤ :=
  Polynomial.X ^ 7 - 8 * Polynomial.X ^ 5 + 19 * Polynomial.X ^ 3 -
    12 * Polynomial.X + 1

end MathlibPlus.Algebra.Claim13230
