import MathlibPlus.Algebra.MonicReciprocal

namespace MathlibPlus.Open.Algebra.Claim58789

/-- Claim 58789: the reciprocal trace evaluation and discriminant normalization,
with the Laurent-polynomial lift retained as the source carrier. -/
def reciprocalTraceDiscriminantClaim : Prop :=
  ∀ {K : Type*} [Field K] (hchar : (2 : K) ≠ 0) (n : ℕ)
    (P Q : Polynomial K),
    MathlibPlus.Algebra.MonicReciprocal.IsMonicReciprocal n P →
    Polynomial.toLaurent P =
      LaurentPolynomial.T (n : ℤ) *
        Polynomial.eval₂ LaurentPolynomial.C
          (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) Q →
    P.eval (1 : K) = Q.eval (2 : K) ∧
      P.eval (-1 : K) = (-1 : K) ^ n * Q.eval (-2 : K) ∧
      Polynomial.discr P =
          (-1 : K) ^ n * P.eval (1 : K) * P.eval (-1 : K) *
            (Polynomial.discr Q) ^ 2 ∧
        Polynomial.discr P =
          Q.eval (2 : K) * Q.eval (-2 : K) * (Polynomial.discr Q) ^ 2 ∧
        ((-1 : K) ^ n * P.eval (1 : K) * P.eval (-1 : K) *
              (Polynomial.discr Q) ^ 2 =
            Q.eval (2 : K) * Q.eval (-2 : K) * (Polynomial.discr Q) ^ 2)

end MathlibPlus.Open.Algebra.Claim58789
