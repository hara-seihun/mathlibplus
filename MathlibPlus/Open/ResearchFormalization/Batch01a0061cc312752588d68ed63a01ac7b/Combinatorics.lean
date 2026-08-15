import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 4359: the one-based Catalan row-set condition. -/
def catalanAdmissibleRowSet (d : ℕ) (K : Fin d → ℕ) : Prop :=
  (∀ i j : Fin d, i.val < j.val → K i < K j) ∧
    (∀ i : Fin d, K i ≤ 2 * (i.val + 1) - 1)

/-- Claim 4361: the lifted endpoint set attached to an ordered row set. -/
def liftedEndpointSet (d : ℕ) (K : Fin d → ℕ) (B : Set ℕ) : Prop :=
  B = {0} ∪ {n | ∃ i : Fin d, n = K i + 1}

end MathlibPlus.Open.ResearchFormalization
