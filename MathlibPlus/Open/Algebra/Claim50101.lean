import MathlibPlus.Basic

namespace MathlibPlus.Open.Algebra

/--
Claim 50101.  The source's polynomial is written over `ℤ`, with the rational
irreducibility check made after coefficient extension to `ℚ`.  Reciprocity is
recorded by equality with `Polynomial.reverse`; noncyclotomic means that the
integral polynomial is not any integral cyclotomic polynomial.  The reduction
clause is coefficientwise polynomial equality, so it retains the multiplicity
at `p = 2`.
-/
def finitePrimeCongruenceUnits_claim50101 : Prop :=
  ∀ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p) →
      Set.Infinite {A : ℕ |
        3 ≤ A ∧
        let P : Polynomial ℤ :=
          Polynomial.X ^ 2 - Polynomial.C (A : ℤ) * Polynomial.X + 1
        P.Monic ∧
        P.reverse = P ∧
        IsUnit P.constantCoeff ∧
        Irreducible (P.map (Int.castRingHom ℚ)) ∧
        (∀ n : ℕ, P ≠ Polynomial.cyclotomic n ℤ) ∧
        (∀ p ∈ S,
          P.map (Int.castRingHom (ZMod p)) =
            Polynomial.X ^ 2 + 1)}

end MathlibPlus.Open.Algebra
