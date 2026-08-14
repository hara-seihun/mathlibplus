import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

def legFactor (a : ℕ) : Polynomial (Polynomial ℤ) :=
  Polynomial.C (Polynomial.X ^ a) +
    Polynomial.X * Polynomial.C (∑ i ∈ Finset.range a, Polynomial.X ^ i)

def claim22251 : Prop :=
  ∀ a : ℕ, 0 < a →
    Polynomial.IsPrimitive (legFactor a) ∧
    legFactor a =
      Polynomial.C (Polynomial.X ^ a) +
        Polynomial.X * Polynomial.C (∑ i ∈ Finset.range a, Polynomial.X ^ i) ∧
    IsCoprime ((Polynomial.X : Polynomial ℤ) ^ a)
      (∑ i ∈ Finset.range a, (Polynomial.X : Polynomial ℤ) ^ i) ∧
    Irreducible (legFactor a) ∧
    ∀ b : ℕ, 0 < b → a ≠ b → ¬ Associated (legFactor a) (legFactor b)

end MathlibPlus.Open.ResearchFormalizationBatch
