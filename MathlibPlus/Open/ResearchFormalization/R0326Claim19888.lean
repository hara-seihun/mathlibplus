import MathlibPlus.Open.Research.FormalizationBatchDecks

namespace MathlibPlus.Open.ResearchFormalization.R0326Claim19888

open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section
open Classical

/-- The graph-valued mixed corner for an actual edge, with its edge witness
retained in the carrier. -/
def mixedCornerCard {n : ℕ} (G : DeckGraph n) (v : Fin n)
    (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet) : DeckGraph (n - 1) :=
  deckDeleteVertexEdge G v e

/-- The isomorphism class of the graph-valued mixed corner. -/
def mixedCornerClass {n : ℕ} (G : DeckGraph n) (v : Fin n)
    (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet) : DeckGraphClass (n - 1) :=
  deckClass (mixedCornerCard G v e he)

/-- The explicit multiplicity-preserving enumeration over every edge and every
vertex, filtered only by nonincidence. -/
def explicitMixedCornerDeck {n : ℕ} (G : DeckGraph n) :
    Multiset (DeckGraphClass (n - 1)) :=
  (((Finset.univ : Finset (Fin n)).product
      (Finset.univ : Finset {e : Sym2 (Fin n) // e ∈ G.edgeSet})).filter
      (fun ve => deckNonincident ve.1 ve.2.1)).val.map
    (fun ve => mixedCornerClass G ve.1 ve.2.1 ve.2.2)

/-- Claim 19888: the individual nonincident corner uses the edge deletion
carrier, and the current mixed-corner deck is exactly its full filtered
multiset enumeration. -/
def nonincidentMixedCorners_claim19888 : Prop :=
  ∀ (n : ℕ) (G : DeckGraph n),
    (∀ (v : Fin n) (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet),
      deckNonincident v e →
        mixedCornerCard G v e he = deckDeleteVertexEdge G v e) ∧
      mixedCornerDeck G = explicitMixedCornerDeck G

end
end MathlibPlus.Open.ResearchFormalization.R0326Claim19888
