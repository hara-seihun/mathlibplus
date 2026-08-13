import Mathlib

namespace MathlibPlus.Algebra.Claim56771

open scoped BigOperators

/-- The algebraic binary-color expansion underlying admitted claim 56771.
The finite type `ι` indexes occurrences in the branch multiset; `m₀` and `m₁`
are the two branch factors. The left side is the sum over all choices of
which branches receive the first central color, and the right side is the
factorized form. -/
theorem binaryFactorization_core_claim56771
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a b t : R) (m₀ m₁ : ι → R) :
    a *
          ∑ S : Finset ι,
            (∏ i ∈ S, (1 + t) * m₀ i) *
              (∏ i ∈ Sᶜ, m₁ i) +
      b *
          ∑ S : Finset ι,
            (∏ i ∈ S, m₀ i) *
              (∏ i ∈ Sᶜ, (1 + t) * m₁ i) =
      a * ∏ i, ((1 + t) * m₀ i + m₁ i) +
        b * ∏ i, (m₀ i + (1 + t) * m₁ i) := by
  rw [← Fintype.prod_add, ← Fintype.prod_add]

end MathlibPlus.Algebra.Claim56771
