import Mathlib
import MathlibPlus.Open.Research.AdmittedBatch019ffedd

namespace MathlibPlus.Open.ResearchFormalization.R0410

open MathlibPlus.Open.Research.AdmittedBatch019ffedd

/-- Claim 21078: two normalized factors cannot both have at least eleven
    members when their union product has five members. -/
def elevenMemberFactorObstruction_claim21078 : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    fiveMemberUnionProductHypotheses A B →
      ¬ (11 ≤ A.card ∧ 11 ≤ B.card)

end MathlibPlus.Open.ResearchFormalization.R0410
