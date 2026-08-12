import Mathlib

set_option linter.style.header false

namespace MathlibPlus.GraphTheory.Claim43514

open SimpleGraph

/-- On a finite labeled vertex set, edge containment and equality of edge
cardinalities force equality of simple graphs. -/
theorem simpleGraph_eq_of_le_of_card_edgeFinset_eq
    {Vertex : Type*}
    [Fintype Vertex]
    {source host : SimpleGraph Vertex}
    [DecidableRel source.Adj]
    [DecidableRel host.Adj]
    (contained : source ≤ host)
    (sameEdgeCard :
      source.edgeFinset.card = host.edgeFinset.card) :
    source = host := by
  classical
  apply SimpleGraph.edgeFinset_inj.mp
  apply Finset.eq_of_subset_of_card_le
  · exact SimpleGraph.edgeFinset_mono contained
  · exact Nat.le_of_eq sameEdgeCard.symm

/-- Proper edge containment on a finite labeled vertex set strictly increases
the number of edges. -/
theorem card_edgeFinset_lt_of_simpleGraph_lt
    {Vertex : Type*}
    [Fintype Vertex]
    {source host : SimpleGraph Vertex}
    [DecidableRel source.Adj]
    [DecidableRel host.Adj]
    (properlyContained : source < host) :
    source.edgeFinset.card < host.edgeFinset.card := by
  classical
  exact Finset.card_lt_card
    (SimpleGraph.edgeFinset_strict_mono properlyContained)

/-- A spanning relabeled copy with the same number of edges is the whole host
graph, not a proper spanning subgraph. -/
theorem simpleGraph_map_eq_of_le_of_card_edgeFinset_eq
    {SourceVertex HostVertex : Type*}
    [Fintype SourceVertex]
    [Fintype HostVertex]
    (source : SimpleGraph SourceVertex)
    (host : SimpleGraph HostVertex)
    [DecidableRel source.Adj]
    [DecidableRel host.Adj]
    (relabel : SourceVertex ≃ HostVertex)
    (contained : source.map relabel.toEmbedding ≤ host)
    (sameEdgeCard :
      source.edgeFinset.card = host.edgeFinset.card) :
    source.map relabel.toEmbedding = host := by
  classical
  apply simpleGraph_eq_of_le_of_card_edgeFinset_eq contained
  rw [SimpleGraph.card_edgeFinset_map]
  exact sameEdgeCard

/-- A spanning relabeled copy with the same number of edges gives an actual
simple-graph isomorphism from the source to the host. -/
theorem simpleGraph_isomorphic_of_spanning_copy_of_card_edgeFinset_eq
    {SourceVertex HostVertex : Type*}
    [Fintype SourceVertex]
    [Fintype HostVertex]
    (source : SimpleGraph SourceVertex)
    (host : SimpleGraph HostVertex)
    [DecidableRel source.Adj]
    [DecidableRel host.Adj]
    (relabel : SourceVertex ≃ HostVertex)
    (contained : source.map relabel.toEmbedding ≤ host)
    (sameEdgeCard :
      source.edgeFinset.card = host.edgeFinset.card) :
    Nonempty (source ≃g host) := by
  classical
  have mappedEqualsHost :
      source.map relabel.toEmbedding = host :=
    simpleGraph_map_eq_of_le_of_card_edgeFinset_eq
      source host relabel contained sameEdgeCard
  subst host
  exact ⟨SimpleGraph.Iso.map relabel source⟩

end MathlibPlus.GraphTheory.Claim43514
