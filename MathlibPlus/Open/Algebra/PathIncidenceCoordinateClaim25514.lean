import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra

/-- Claim 25514: prefix currents for a full-support path relation telescope
in every field after translating the source's one-based indices to naturals. -/
def pathIncidenceCoordinateFormula_claim25514 : Prop :=
  ∀ {K : Type*} [Field K] (m : ℕ) (a : ℕ → K),
    (∑ i ∈ Finset.range m, a i) = 0 →
      let b : ℕ → K := fun j => ∑ i ∈ Finset.range j, a i
      b 0 = 0 ∧
        b m = 0 ∧
          ∀ i, i < m → a i = b (i + 1) - b i

end MathlibPlus.Open.Algebra
