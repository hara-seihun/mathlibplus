import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 34987: the sharp edge floor for a finite simple graph whose every
five-vertex induced subgraph contains a cycle. -/
def inducedForestFourSharpEdgeFloor_claim34987 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V),
    8 ≤ Fintype.card V →
      (∀ s : Finset V, s.card = 5 →
        ¬ (G.induce (↑s : Set V)).IsAcyclic) →
      G.edgeSet.ncard ≥
        (Fintype.card V * (Fintype.card V - 2) + 3) / 4

end MathlibPlus.Open.GraphTheory
