import Mathlib

namespace MathlibPlus.GraphTheory.Claim28295

open scoped BigOperators

/-- The component sizes of a finite graph, including every spanning isolated
vertex as a component of size one. -/
noncomputable def componentSizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : Multiset ℕ := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  exact (Finset.univ : Finset H.ConnectedComponent).val.map
    (fun c => c.supp.ncard)

/-- The component sizes add up to the number of vertices. -/
theorem componentSizes_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) :
    (componentSizes H).sum = Fintype.card V := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  change (∑ c ∈ (Finset.univ : Finset H.ConnectedComponent), c.supp.ncard) = _
  rw [← (set_fintype_card_eq_univ_iff _).mpr H.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion SimpleGraph.ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent H hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card']

/-- A multiset of component sizes, viewed as an integer partition. -/
noncomputable def componentPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : Nat.Partition (Fintype.card V) :=
  Nat.Partition.ofSums _ (componentSizes H) (componentSizes_sum H)

/-- No zero part is removed: every connected component has a nonempty support. -/
theorem componentPartition_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) :
    (componentPartition H).parts = componentSizes H := by
  classical
  rw [componentPartition, Nat.Partition.ofSums_parts]
  apply Multiset.filter_eq_self.mpr
  intro n hn
  obtain ⟨c, _, rfl⟩ := Multiset.mem_map.1 hn
  exact ((Set.ncard_pos (s := c.supp) (Set.toFinite _)).2
    (SimpleGraph.ConnectedComponent.nonempty_supp c)).ne'

/-- The graph on the same vertex type whose edge set is the chosen edge set.
The separate hypothesis in the claim records that the chosen edges lie in the
edge set of the ambient simple graph. -/
def spanningSubgraph
    {V : Type*} (G : SimpleGraph V) (S : Finset (Sym2 V))
    (_hS : (S : Set (Sym2 V)) ⊆ G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

theorem spanningSubgraph_le
    {V : Type*} (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet) :
    spanningSubgraph G S hS ≤ G := by
  intro v w h
  exact hS ((SimpleGraph.fromEdgeSet_adj (S : Set (Sym2 V))).mp h).1

/-- The partition `λ_G(S)` of the spanning subgraph `(V,S)`. -/
noncomputable def componentSizePartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet) : Nat.Partition (Fintype.card V) :=
  componentPartition (spanningSubgraph G S hS)

/-- The parts of `λ_G(S)` are exactly the sizes of all connected components of
`(V,S)`, so isolated vertices are retained. -/
theorem componentSizePartition_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet) :
    (componentSizePartition G S hS).parts =
      componentSizes (spanningSubgraph G S hS) := by
  exact componentPartition_parts _

end MathlibPlus.GraphTheory.Claim28295
