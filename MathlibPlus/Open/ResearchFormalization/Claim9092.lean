import MathlibPlus.Open.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim9092

open MathlibPlus.Open.FormalizationBatch

/-- Claim 9092: a Boolean coloring constant on every component of the
constraint graph produces the two labeled graph-bit projections and realizes
all prescribed pointed card isomorphisms. -/
def claim9092_componentColoringsProduceCompatibleGraphPairs : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (π : PointedLocalPermutations V)
    (c : GammaVertex V → Bool),
    IsGammaComponentColoring π c →
      RealizesPrescribedCardIsomorphisms π
        (componentColoringProjection π c).1
        (componentColoringProjection π c).2

end MathlibPlus.Open.ResearchFormalization.Claim9092
