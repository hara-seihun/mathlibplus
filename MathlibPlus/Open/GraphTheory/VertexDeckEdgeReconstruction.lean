import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory

/-- Claim 23402: the edge counts of all vertex-deleted cards determine the edge count. -/
def vertexDeckEdgeReconstruction : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    (∑ v : V, (G.induce {v}ᶜ).edgeSet.ncard) =
      (Fintype.card V - 2) * G.edgeSet.ncard ∧
      (3 ≤ Fintype.card V →
        G.edgeSet.ncard =
          (∑ v : V, (G.induce {v}ᶜ).edgeSet.ncard) /
            (Fintype.card V - 2))

end MathlibPlus.Open.GraphTheory
