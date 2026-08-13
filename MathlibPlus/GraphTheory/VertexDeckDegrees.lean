import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The degree of each vertex is recovered from the total edge count and its
vertex-deleted card, with `G-v` represented by the induced graph on `{v}ᶜ`. -/
def vertexDeckDegreesReconstructible : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V),
    G.degree v = G.edgeFinset.card - (G.induce {v}ᶜ).edgeFinset.card

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.GraphTheory

theorem vertexDeckDegreesReconstructible_proved :
    MathlibPlus.Open.GraphTheory.vertexDeckDegreesReconstructible := by
  intro V hFintype hDecidableEq G hDecidableAdj v
  have hcard := G.card_edgeFinset_induce_compl_singleton v
  rw [G.card_edgeFinset_deleteIncidenceSet v] at hcard
  have hle : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset
  omega

end MathlibPlus.GraphTheory
