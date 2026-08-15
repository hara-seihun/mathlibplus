import Mathlib

namespace MathlibPlus.Open.Graph

noncomputable def componentSizePartition {V : Type*} [Fintype V]
    (H : SimpleGraph V) : Multiset ℕ :=
  (Finset.univ : Finset H.ConnectedComponent).val.map
    (fun C => (C : Set V).ncard)

noncomputable def lambdaG {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set (Sym2 V)) : Multiset ℕ :=
  componentSizePartition (SimpleGraph.fromEdgeSet S)

def isolatedVertexContributesOnePart {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set (Sym2 V)) (v : V) : Prop :=
  S ⊆ G.edgeSet →
    (∀ w : V, s(v, w) ∉ S) →
      (↑((SimpleGraph.fromEdgeSet S).connectedComponentMk v) = ({v} : Set V)) ∧
        1 ∈ lambdaG G S

end MathlibPlus.Open.Graph
