import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim31499

open SimpleGraph

/-- A connected finite graph has at least one fewer edge than vertices. -/
theorem connected_edge_lower_bound
    {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    Nat.card V ≤ Nat.card G.edgeSet + 1 := by
  exact hG.card_vert_le_card_edgeSet_add_one

/-- At the minimum edge count, connectedness is equivalent to being a tree. -/
theorem tree_iff_connected_edge_minimum
    {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  exact isTree_iff_connected_and_card

/-- A graph with fewer than the minimum connected edge count is disconnected. -/
theorem disconnected_of_edge_count_below_vertices
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (h : Nat.card G.edgeSet + 1 < Nat.card V) : ¬ G.Connected := by
  intro hG
  exact (not_lt_of_ge hG.card_vert_le_card_edgeSet_add_one) h

end MathlibPlus.GraphTheory.Claim31499
