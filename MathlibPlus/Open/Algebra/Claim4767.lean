import MathlibPlus.Algebra.Claim4764

namespace MathlibPlus.Open.Algebra.Claim4767

noncomputable section

private def jensenPolynomial {R : Type*} [CommRing R]
    (a : ℕ → R) (d n : ℕ) : Polynomial R :=
  ∑ j ∈ Finset.range (d + 1),
    (Polynomial.monomial j) ((d.choose j : R) * a (n + j))

/-- The Jensen-polynomial family has compatible Pascal and differential shifts. -/
def latticeCompatibility {R : Type*} [CommRing R] (a : ℕ → R) : Prop :=
  ∀ d n,
    (jensenPolynomial a (d + 1) n =
        jensenPolynomial a d n + Polynomial.X * jensenPolynomial a d (n + 1)) ∧
    (1 ≤ d →
      Polynomial.derivative (jensenPolynomial a d n) =
        (d : R) • jensenPolynomial a (d - 1) (n + 1)) ∧
    (1 ≤ d →
      (Polynomial.derivative (jensenPolynomial a (d + 1) n) =
          Polynomial.derivative (jensenPolynomial a d n) +
            jensenPolynomial a d (n + 1) +
            Polynomial.X * Polynomial.derivative (jensenPolynomial a d (n + 1))) ∧
      (((d + 1 : ℕ) : R) • jensenPolynomial a d (n + 1) =
          (d : R) • jensenPolynomial a (d - 1) (n + 1) +
            jensenPolynomial a d (n + 1) +
            Polynomial.X * ((d : R) • jensenPolynomial a (d - 1) (n + 2))))

end

end MathlibPlus.Open.Algebra.Claim4767
