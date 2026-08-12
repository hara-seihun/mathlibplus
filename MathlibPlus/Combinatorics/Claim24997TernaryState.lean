import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim24997

/-- The elementary symmetric sum of degree `k` over an indexed occurrence set.
Indexing by `Fin 6` preserves repeated cavity values as distinct occurrences. -/
noncomputable def elementarySymmetric
    {R : Type*} [CommSemiring R]
    (k : ℕ) (I : Finset (Fin 6)) (a : Fin 6 → R) : R :=
  ∑ J ∈ I.powersetCard k, ∏ i ∈ J, a i

/-- The varying degree-two ternary hypermatching state for a triple and its
complement, as displayed in claim 24997. -/
noncomputable def ternaryHypermatchingState
    {R : Type*} [CommSemiring R]
    (a : Fin 6 → R) (E : Finset (Fin 6)) (_hE : E.card = 3) : R × R :=
  (elementarySymmetric 2 E a +
      elementarySymmetric 2 (Finset.univ \ E) a,
    elementarySymmetric 3 E a +
      elementarySymmetric 3 (Finset.univ \ E) a)

end MathlibPlus.Combinatorics.Claim24997
