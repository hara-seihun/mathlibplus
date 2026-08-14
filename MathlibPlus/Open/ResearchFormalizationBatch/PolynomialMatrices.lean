import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.PolynomialMatrices

def laurentUnimodular
    (K : Type*) [Field K] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (Polynomial K)) (r : ℕ) : Prop :=
  ∃ u : Kˣ,
    Matrix.det M = Polynomial.C (u : K) * Polynomial.X ^ r

def monomialDeterminantLaurentInvertibility
    (K : Type*) [Field K] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (Polynomial K)) : Prop :=
  let ι : Polynomial K →+* LaurentPolynomial K :=
    Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T 1)
  (∀ (u : Kˣ) (r : ℕ),
      Matrix.det M = Polynomial.C (u : K) * Polynomial.X ^ r →
        IsUnit (Matrix.map M ι)) ∧
    (IsUnit (Matrix.map M ι) →
      ∃ (u : Kˣ) (k : ℤ),
        ι (Matrix.det M) = LaurentPolynomial.C (u : K) * LaurentPolynomial.T k ∧
          0 ≤ k)

def orderedBranchThreeCoordinateCount : Prop :=
  ∀ E : ℕ, 18 ≤ E →
    Fintype.card
        {c : Fin (E + 1) × (Fin 5 → Fin 2) × Fin (E + 1) //
          0 < c.1.val ∧
            0 < c.2.2.val ∧
            c.1.val + c.2.2.val + 5 + ∑ i, (c.2.1 i).val = E} =
      32 * E - 272

end MathlibPlus.Open.ResearchFormalizationBatch.PolynomialMatrices
