import MathlibPlus.Algebra.Claim50754

open scoped LaurentPolynomial

namespace MathlibPlus.Open.Algebra.Claim50758

/-- The imposed Laurent quotient has the stated nonzero torsion class, while
its outer factor is nonvanishing on the open character strip. -/
def stripNonvanishingTorsion : Prop :=
  let A := ℚ[T;T⁻¹]
  let q : A := LaurentPolynomial.T 1
  let pIn : A := (5 * q + 4) * (4 * q + 5)
  let pOut : A := (2 * q + 1) * (q + 2)
  let p : A := pIn * pOut
  let I := Ideal.span ({p} : Set A)
  let Q := A ⧸ I
  let characterValue : ℂ → ℂ := fun ρ =>
    Complex.exp (((1 / 2 : ℂ) - ρ) * (Real.log 2 : ℂ))
  (Ideal.Quotient.mk I pOut) * (Ideal.Quotient.mk I pIn) = 0 ∧
    Ideal.Quotient.mk I pIn ≠ 0 ∧
    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      (2 * characterValue ρ + 1) * (characterValue ρ + 2) ≠ 0) ∧
    ¬ IsUnit (Ideal.Quotient.mk I pOut : Q)

end MathlibPlus.Open.Algebra.Claim50758
