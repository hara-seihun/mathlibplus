import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim20663

/-- Lehmer's degree-ten reciprocal polynomial. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1

/-- The Mahler measure of the complexification of Lehmer's polynomial. -/
noncomputable def lehmerNumber : ℝ :=
  Polynomial.mahlerMeasure (lehmerPolynomial.map (algebraMap ℤ ℂ))

end MathlibPlus.Algebra.Claim20663
