import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

namespace MathlibPlus.Open.ResearchFormalization.R0532Claim29371

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR0532

/-- Claim 29371: with positive trunk and leg lengths, at least two legs on
both sides, and equal side totals, equality of the exact first CSF deck layer
forces isomorphism up to exchanging the two sides, with no trunk-length or
side-count restriction beyond admissibility. -/
def equalTotalDoubleSpiderFirstDeckReconstructs_claim29371 : Prop :=
  ∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T →
      equalTotalDoubleSpider T' →
        firstDeckLayer T = firstDeckLayer T' →
          sideExchangeEquivalent T T'

end

end MathlibPlus.Open.ResearchFormalization.R0532Claim29371
