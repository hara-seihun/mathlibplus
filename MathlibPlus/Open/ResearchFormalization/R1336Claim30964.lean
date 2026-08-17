import MathlibPlus.Open.ResearchFormalization.R1336SmallGroupAudit

namespace MathlibPlus.Open.ResearchFormalization.R1336Claim30964

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1336

/-- Claim 30964: every automorphism of every normal section of the exact
QuaternionGroup 3 carrier has order among `1,2,3,6`; an order-seven relation
therefore forces the identity. -/
def noOrderSevenSectionAutomorphism_claim30964 : Prop :=
  ∀ L : Subgroup Q12, ∀ N : Subgroup L, (hN : N.Normal) →
    letI : N.Normal := hN
    ∀ φ : (L ⧸ N) ≃* (L ⧸ N),
      (orderOf φ = 1 ∨ orderOf φ = 2 ∨ orderOf φ = 3 ∨ orderOf φ = 6) ∧
        (φ ^ 7 = 1 → φ = 1)

end

end MathlibPlus.Open.ResearchFormalization.R1336Claim30964
