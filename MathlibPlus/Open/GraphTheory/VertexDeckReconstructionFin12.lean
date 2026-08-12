import Mathlib.Combinatorics.SimpleGraph.Basic

namespace MathlibPlus.Open.GraphTheory

/-- Claim 20374: equality of the full vertex decks of two twelve-vertex graphs
forces the graphs to be isomorphic.  The deck equality is expressed as a
permutation matching the deleted vertices and an isomorphism of the resulting
induced graphs. -/
def vertexDeckReconstructionFin12_claim20374 : Prop :=
  ∀ G H : SimpleGraph (Fin 12),
    (∃ σ : Equiv.Perm (Fin 12),
      ∀ v : Fin 12,
        ∃ e : {w : Fin 12 // w ≠ v} ≃ {w : Fin 12 // w ≠ σ v},
          ∀ x y,
            G.Adj x.1 y.1 ↔ H.Adj (e x).1 (e y).1) →
      ∃ e : Equiv.Perm (Fin 12),
        ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

end MathlibPlus.Open.GraphTheory
