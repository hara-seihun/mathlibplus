import MathlibPlus.Open.ResearchFormalization.C0095Claim1452
import MathlibPlus.Open.ResearchBatch.C0095

namespace MathlibPlus.Open.ResearchFormalization.C0095Claim1454

open MathlibPlus.Open.ResearchBatch.C0095
open MathlibPlus.Open.ResearchFormalization.C0095
open MathlibPlus.NumberTheory.BellottiGrowth

noncomputable section

/-- The full-domain Hurwitz-zeta-difference bound with the exact transferred
Bellotti pair and the complete 0<u≤1, 1/2≤sigma≤1, |t|≥3 domain. -/
def fullDomainHurwitzDifferenceBound_claim1454 : Prop :=
  ∀ (t σ u : ℝ),
    3 ≤ |t| →
    1 / 2 ≤ σ →
    σ ≤ 1 →
    0 < u →
    u ≤ 1 →
    ‖hurwitzDifference u σ t‖ ≤
      vkEnvelope bellottiAStar bellottiBStar σ t

end

end MathlibPlus.Open.ResearchFormalization.C0095Claim1454
