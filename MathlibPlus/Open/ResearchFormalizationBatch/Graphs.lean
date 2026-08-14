import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Graphs

/-- Claim 44874: the zero minimum-card shell is a star, possibly with isolated vertices. -/
def claim44874 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
    G.edgeFinset.card - G.maxDegree = 0 ↔
      (G.edgeFinset.card = 0 ∨
        ∃ c : V, ∀ ⦃u v : V⦄, G.Adj u v → u = c ∨ v = c)

end MathlibPlus.Open.ResearchFormalizationBatch.Graphs
