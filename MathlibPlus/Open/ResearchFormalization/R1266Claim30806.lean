import MathlibPlus.Open.Research.FormalizationBatch.R1266Claim30808

namespace MathlibPlus.Open.ResearchFormalization.R1266Claim30806

open MathlibPlus.Open.Research.R1266

noncomputable section

/-- Claim 30806: every root-balanced double-star quadratic in the exact
    RationalFunction carrier is irreducible over `ℚ(x)`. -/
def doubleStarQuadraticIrreducible_claim30806 : Prop :=
  ∀ a b : ℕ, rootBalanced a b →
    (P a b).natDegree = 2 ∧ Irreducible (P a b)

end

end MathlibPlus.Open.ResearchFormalization.R1266Claim30806
