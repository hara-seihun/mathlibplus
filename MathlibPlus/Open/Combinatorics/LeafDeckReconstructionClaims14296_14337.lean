import MathlibPlus.Open.Combinatorics.FiniteGraphDeckClaims
import MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

namespace MathlibPlus.Open.Combinatorics.LeafDeckReconstructionClaims

open MathlibPlus.Open.Combinatorics.FiniteGraphDeck
open MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

/-- Trees in the finite-graph carrier are determined by their leaf decks. -/
def claim14296 : Prop :=
  ∀ (T T' : FiniteGraph),
    T.2.IsTree → T'.2.IsTree →
      leafDeck T = leafDeck T' →
        Nonempty (T.2 ≃g T'.2)

/-- The leaf-deck invariant separates the finite tree types in the stated
order range. -/
def claim14337 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    ∀ (T U : {G : SimpleGraph (Fin n) // G.IsTree}),
      leafDeck14336 T.1 = leafDeck14336 U.1 →
        Nonempty (T.1 ≃g U.1)

end MathlibPlus.Open.Combinatorics.LeafDeckReconstructionClaims
