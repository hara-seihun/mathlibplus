import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 29429: an order-12 graph with 31 edges and a cycle in every
five-vertex induced subgraph has triangle-free complement. -/
def order12ThirtyOneComplementTriangleFree_claim29429 : Prop :=
  ∀ (G : SimpleGraph (Fin 12)),
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    G.edgeFinset.card = 31 →
      (∀ s : Finset (Fin 12), s.card = 5 →
        ∃ (v : (↑s : Set (Fin 12))),
          ∃ w : (G.induce (↑s : Set (Fin 12))).Walk v v, w.IsCycle) →
      Gᶜ.CliqueFree 3

end MathlibPlus.Open.GraphTheory
