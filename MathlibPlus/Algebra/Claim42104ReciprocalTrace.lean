import Mathlib

namespace MathlibPlus.Algebra.Claim42104

open scoped LaurentPolynomial

noncomputable section

/-- The degree-seven odd polynomial in the trace variable. -/
def tracePolynomial42104 : Polynomial ℚ :=
  Polynomial.X ^ 7 - 8 * Polynomial.X ^ 5 + 19 * Polynomial.X ^ 3 -
    12 * Polynomial.X + 1

/-- The reciprocal degree-fourteen polynomial. -/
def reciprocalPolynomial42104 : Polynomial ℚ :=
  Polynomial.X ^ 14 - Polynomial.X ^ 12 + Polynomial.X ^ 7 -
    Polynomial.X ^ 2 + 1

/-- The exact Laurent-polynomial reciprocal trace lift. -/
def exactReciprocalTraceLift_claim42104 : Prop :=
  Polynomial.toLaurent (reciprocalPolynomial42104) =
    LaurentPolynomial.T (7 : ℤ) *
      Polynomial.eval₂ LaurentPolynomial.C
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
        tracePolynomial42104

end

end MathlibPlus.Algebra.Claim42104
