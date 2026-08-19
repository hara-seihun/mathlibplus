import MathlibPlus.Open.Combinatorics.FiniteGraphDeckClaims

namespace MathlibPlus.Open.Combinatorics.Claim44782

open MathlibPlus.Open.Combinatorics.FiniteGraphDeck

/-- The canonical two-vertex complete and edgeless finite graphs. -/
def completeTwo : FiniteGraph :=
  ⟨2, (⊤ : SimpleGraph (Fin 2))⟩

def emptyTwo : FiniteGraph :=
  ⟨2, (⊥ : SimpleGraph (Fin 2))⟩

def completeOne : FiniteGraph :=
  ⟨1, (⊥ : SimpleGraph (Fin 1))⟩

/-- Deleting either vertex from either displayed two-vertex graph produces the
same one-vertex graph class, and the full vertex-deck multiplicities retain
both copies. -/
def claim44782_twoVertexDeckMultiplicity : Prop :=
  (∀ v : Fin 2,
    graphClass (deletedFiniteGraph (⊤ : SimpleGraph (Fin 2)) v) =
      graphClass completeOne) ∧
  (∀ v : Fin 2,
    graphClass (deletedFiniteGraph (⊥ : SimpleGraph (Fin 2)) v) =
      graphClass completeOne) ∧
  vertexDeck completeTwo = Multiset.replicate 2 (graphClass completeOne) ∧
  vertexDeck emptyTwo = Multiset.replicate 2 (graphClass completeOne)

end MathlibPlus.Open.Combinatorics.Claim44782
