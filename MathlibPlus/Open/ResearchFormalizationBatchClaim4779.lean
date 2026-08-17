import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The generating polynomial on the interval `[a,b)` of a finite coefficient vector. -/
noncomputable def truncatedIntervalGeneratingPolynomial_claim4779
    {R : Type*} [CommSemiring R] {n : ℕ}
    (c : Fin n → R) (a b : ℕ) (_ha : a < b) (_hb : b ≤ n) : Polynomial R :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => a ≤ j.1 ∧ j.1 < b),
    Polynomial.C (c j) * Polynomial.X ^ (j.1 - a)

end MathlibPlus.Open.ResearchFormalizationBatch
