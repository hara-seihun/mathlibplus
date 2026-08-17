import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

namespace MathlibPlus.Open.ResearchFormalization.BatchR0532

/-- Claim 29372: equal-total admissible double spiders with equal first deck
layers have equal common side totals, complete global leg multisets, and trunk
lengths; each trunk length is its order minus one minus twice its side total. -/
def globalRecoveryUnderEqualTotal_claim29372 : Prop :=
  ∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T →
    equalTotalDoubleSpider T' →
    firstDeckLayer T = firstDeckLayer T' →
    sideTotal T = sideTotal T' ∧
      globalLegMultiset T = globalLegMultiset T' ∧
        T.trunk = T'.trunk ∧
          T.trunk = doubleSpiderOrder T - 1 - 2 * sideTotal T ∧
            T'.trunk = doubleSpiderOrder T' - 1 - 2 * sideTotal T'

end MathlibPlus.Open.ResearchFormalization.BatchR0532
