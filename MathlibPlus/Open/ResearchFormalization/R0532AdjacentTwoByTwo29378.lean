import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

namespace MathlibPlus.Open.ResearchFormalization.R0532AdjacentTwoByTwo29378

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR0532

/-- Claim 29378: the exact adjacent 2-by-2 implication in the equal-total
 double-spider reconstruction carrier. -/
def claim29378 : Prop :=
  ∀ (T T' : DoubleSpider),
    equalTotalDoubleSpider T →
      equalTotalDoubleSpider T' →
        caseAdjacentTwoByTwo T →
          caseAdjacentTwoByTwo T' →
            firstDeckLayer T = firstDeckLayer T' →
              sideExchangeEquivalent T T'

end

end MathlibPlus.Open.ResearchFormalization.R0532AdjacentTwoByTwo29378
