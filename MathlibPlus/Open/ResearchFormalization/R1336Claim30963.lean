import MathlibPlus.Open.ResearchFormalization.R1336SmallGroupAudit

namespace MathlibPlus.Open.ResearchFormalization.R1336Claim30963

open MathlibPlus.Open.ResearchFormalization.R1336

/-- The exact normal-subgroup order set of `Q₁₂`. -/
def q12NormalSubgroupOrderSet : Set ℕ :=
  ({1, 2, 3, 6, 12} : Set ℕ)

/-- Claim 30963: every subgroup of the exact `Q₁₂ = QuaternionGroup 3` carrier
    is cyclic or is all of `Q₁₂`; cyclic subgroups have the unique subgroup of
    each dividing order; and equal-order normal subgroups are rigid both in
    `Q₁₂` and in every subgroup of `Q₁₂`. -/
def claim30963_q12SubgroupAndNormalSubgroupRigidity : Prop :=
  (∀ L : Subgroup Q12, IsCyclic L ∨ L = ⊤) ∧
    (∀ L : Subgroup Q12, IsCyclic L →
      ∀ d : ℕ, d ∣ Nat.card L →
        ∃! M : Subgroup L, Nat.card M = d) ∧
      normalSubgroupOrders = q12NormalSubgroupOrderSet ∧
        (∀ N M : Subgroup Q12,
          N.Normal → M.Normal → Nat.card N = Nat.card M → N = M) ∧
          (∀ L : Subgroup Q12,
            ∀ N M : Subgroup L,
              N.Normal → M.Normal → Nat.card N = Nat.card M → N = M)

end MathlibPlus.Open.ResearchFormalization.R1336Claim30963
