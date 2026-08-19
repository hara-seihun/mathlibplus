import MathlibPlus.Open.ResearchFormalization.C0095Claim1452
import MathlibPlus.Open.ResearchBatch.C0095

namespace MathlibPlus.Open.ResearchFormalization.C0095Claim1456

open MathlibPlus.NumberTheory.BellottiGrowth
open MathlibPlus.Open.ResearchBatch.C0095
open MathlibPlus.Open.ResearchFormalization.C0095

noncomputable section

/-- The two published exponent-four lower envelopes are dominated by the
exact transferred Bellotti pair throughout the common half-to-one strip. -/
def lowerEnvelopeDomination_claim1456 : Prop :=
  (58.1 < 70.6199 ∧
    70.6199 < bellottiAStar ∧
    58.1 < bellottiAStar ∧
    4 < bellottiBStar) ∧
  ∀ (σ t : ℝ),
    1 / 2 ≤ σ →
    σ ≤ 1 →
    1 < |t| →
    publishedVKEnvelope 70.6199 σ t ≤
        vkEnvelope bellottiAStar bellottiBStar σ t ∧
      publishedVKEnvelope 58.1 σ t ≤
        vkEnvelope bellottiAStar bellottiBStar σ t

end

end MathlibPlus.Open.ResearchFormalization.C0095Claim1456
