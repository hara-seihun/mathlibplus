import MathlibPlus.Open.NumberTheory.Claim9756

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim9749

/-- Prime-exponent factorization of the gcd Gram kernel and its local AR(1)
realization.  The finite product is the tensor product over the prime support. -/
def claim9749 : Prop :=
  (∀ d e : ℕ, 0 < d → 0 < e →
    ((Nat.gcd d e : ℝ) ^ 2) / ((d : ℝ) * (e : ℝ)) =
      Finset.prod
        (MathlibPlus.Open.NumberTheory.Claim9756.primeTensorSupport d e)
        (fun p =>
          ((p : ℝ)⁻¹) ^
            Nat.dist
              (MathlibPlus.Open.NumberTheory.Claim9756.primeExponent d p)
              (MathlibPlus.Open.NumberTheory.Claim9756.primeExponent e p))) ∧
  (∀ p : ℕ, p.Prime →
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] (f : ℕ → H),
      MathlibPlus.Open.NumberTheory.Claim9756.orthonormalInnovationFamily f →
      ∀ a b : ℕ,
        ⟪MathlibPlus.Open.NumberTheory.Claim9756.localPrimeAR1Vector p f a,
          MathlibPlus.Open.NumberTheory.Claim9756.localPrimeAR1Vector p f b⟫ =
          ((p : ℝ)⁻¹) ^ Nat.dist a b)

end MathlibPlus.Open.NumberTheory.Claim9749
