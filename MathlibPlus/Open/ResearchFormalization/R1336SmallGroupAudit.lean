import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1336

/-- The dicyclic/generalized-quaternion group denoted by `Q₁₂` in the audit. -/
abbrev Q12 := QuaternionGroup 3

/-- Orders of all normal subgroups of the displayed `Q₁₂`. -/
def normalSubgroupOrders : Set ℕ :=
  {n | ∃ L : Subgroup Q12, L.Normal ∧ n = Nat.card L}

/-- Orders occurring among the group automorphisms in the audit. -/
def automorphismOrders : Set ℕ :=
  Set.range (fun φ : Q12 ≃* Q12 => orderOf φ)

/-- Claim 30971: the exact subgroup and automorphism audit for `Q₁₂`. -/
def exactSmallGroupAudit_30971 : Prop :=
  Fintype.card (Subgroup Q12) = 8 ∧
    Fintype.card (Q12 ≃* Q12) = 12 ∧
    normalSubgroupOrders = ({1, 2, 3, 6, 12} : Set ℕ) ∧
    automorphismOrders = ({1, 2, 3, 6} : Set ℕ) ∧
    ∀ φ : Q12 ≃* Q12, orderOf φ ≠ 7

end MathlibPlus.Open.ResearchFormalization.R1336
