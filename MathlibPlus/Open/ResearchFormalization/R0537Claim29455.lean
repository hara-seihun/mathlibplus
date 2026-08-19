import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0537Claim29455

/-- The scalar multiplying the common normal direction in the distinct-shadow
barycentric law.  The product is over all shadows other than the selected one.
-/
def barycentricWeight {K : Type*} [Field K] {d : ℕ}
    (lambda : Fin d → K) (i : Fin d) : K :=
  (-lambda i) ^ (d - 1) /
    (Finset.univ.erase i).prod (fun j => lambda j - lambda i)

/-- The exact first-linear data retained in the squarefree distinct-shadow
branch: normal coordinates start at index two, Record 21 bounds every
nonzero common-direction coordinate, and the first-jet coefficients obey the
barycentric law. -/
def squarefreeDistinctShadowFirstLinearTrade
    {K : Type*} [Field K]
    (m d : ℕ) (lambda : Fin d → K)
    (C : Fin m → K) (S : Fin d → Fin m → K) : Prop :=
  (∀ s : Fin m, C s ≠ 0 → 2 ≤ s.1) ∧
    (∀ s : Fin m, C s ≠ 0 → s.1 ≤ m - 2 * (d - 1)) ∧
    (∀ i : Fin d, ∀ s : Fin m,
      S i s = barycentricWeight lambda i * C s)

/-- Claim 29455.  With distinct independence shadows, the normal-coordinate
bound from Record 21 has no available coordinate once the number of factors
exceeds half the common order.  Thus the common direction and every first-jet
coefficient vanish, and there is no nonzero trade of this kind. -/
def noNonzeroFirstLinearTrade_whenDense_claim29455 : Prop :=
  ∀ {K : Type*} [Field K] (m d : ℕ) (lambda : Fin d → K),
    d > m / 2 →
      (∀ i j : Fin d, i ≠ j → lambda i ≠ lambda j) →
        (∀ (C : Fin m → K) (S : Fin d → Fin m → K),
          squarefreeDistinctShadowFirstLinearTrade m d lambda C S →
            C = 0 ∧ (∀ i : Fin d, S i = 0)) ∧
          ¬ (∃ (C : Fin m → K) (S : Fin d → Fin m → K),
            squarefreeDistinctShadowFirstLinearTrade m d lambda C S ∧
              C ≠ 0)

end MathlibPlus.Open.ResearchFormalization.R0537Claim29455
