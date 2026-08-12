import Mathlib.Algebra.Polynomial.Monic

namespace MathlibPlus.Algebra

/-- Claim 24697: two monic rational polynomials cannot be proportional by a
rational scalar other than one. The source's matching products are represented
by the two polynomials, and their common unit leading coefficient by monicity. -/
theorem rationalProportionalityScalar_eq_one_claim24697
    (P Q : Polynomial ℚ) (scalar : ℚ)
    (hP : P.Monic) (hQ : Q.Monic)
    (hprop : Q = scalar • P) :
    scalar = 1 := by
  have h := congrArg Polynomial.leadingCoeff hprop
  simpa [Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul, hP.leadingCoeff,
    hQ.leadingCoeff] using h.symm

end MathlibPlus.Algebra
