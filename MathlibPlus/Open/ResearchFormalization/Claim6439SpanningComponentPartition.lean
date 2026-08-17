import MathlibPlus.Open.Graph.IsolatedVertexPart

namespace MathlibPlus.Open.ResearchFormalization.Claim6439SpanningComponentPartition

/-- Claim 6439: `lambdaG` is the component-size partition of the spanning
subgraph on the full vertex set, including singleton components. -/
def componentSizePartitionOfSpanningSubgraph_claim6439 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set (Sym2 V)),
    S ⊆ G.edgeSet →
      let H := SimpleGraph.fromEdgeSet S
      let part := MathlibPlus.Open.Graph.lambdaG G S
      (∀ C : H.ConnectedComponent,
        (C : Set V).Nonempty ∧ (C : Set V).ncard ∈ part) ∧
      (∀ n : ℕ, n ∈ part →
        ∃ C : H.ConnectedComponent, n = (C : Set V).ncard) ∧
      part.sum = Fintype.card V ∧
      (∀ n : ℕ, n ∈ part → 0 < n) ∧
      (∀ v : V,
        (∀ w : V, s(v, w) ∉ S) →
          (↑(H.connectedComponentMk v) = ({v} : Set V)) ∧ 1 ∈ part)

end MathlibPlus.Open.ResearchFormalization.Claim6439SpanningComponentPartition
