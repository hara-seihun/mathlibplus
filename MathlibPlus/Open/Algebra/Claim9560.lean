import Mathlib

namespace MathlibPlus.Open.Algebra.Claim9560

/-- The Laurent involution descends to the nontrivial quadratic conjugation on the quotient field. -/
def laurentInvolutionDescends : Prop :=
  let R := LaurentPolynomial ℚ
  let u : R := LaurentPolynomial.T 1
  let f : R := u + LaurentPolynomial.T (-1) - 3
  let I : Ideal R := Ideal.span ({f} : Set R)
  let Q := R ⧸ I
  let g : Polynomial ℚ := Polynomial.X ^ 2 - 3 * Polynomial.X + 1
  let K := AdjoinRoot g
  IsField K ∧
    ∃ ι : R ≃+* R,
      (∀ n : ℤ, ι (LaurentPolynomial.T n) = LaurentPolynomial.T (-n)) ∧
      (∀ q : ℚ, ι (LaurentPolynomial.C q) = LaurentPolynomial.C q) ∧
      ι.trans ι = RingEquiv.refl R ∧
      ι f = f ∧
      ∃ τ : Q ≃+* Q,
        (∀ r : R, τ (Ideal.Quotient.mk I r) = Ideal.Quotient.mk I (ι r)) ∧
        ∃ e : Q ≃+* K,
          (∀ q : ℚ,
            e (Ideal.Quotient.mk I (LaurentPolynomial.C q)) = algebraMap ℚ K q) ∧
          e (Ideal.Quotient.mk I u) = AdjoinRoot.root g ∧
          e (Ideal.Quotient.mk I (LaurentPolynomial.T (-1))) =
            (3 : K) - AdjoinRoot.root g ∧
          ∃ σ : K ≃+* K,
            σ ≠ RingEquiv.refl K ∧
            σ.trans σ = RingEquiv.refl K ∧
            σ (AdjoinRoot.root g) = (3 : K) - AdjoinRoot.root g ∧
            (AdjoinRoot.root g) * ((3 : K) - AdjoinRoot.root g) = 1 ∧
            (∀ q : ℚ,
              σ (algebraMap ℚ K q) = algebraMap ℚ K q) ∧
            ∀ y : Q, e (τ y) = σ (e y)

end MathlibPlus.Open.Algebra.Claim9560
