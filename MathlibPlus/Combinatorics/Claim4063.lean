import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MathlibPlus.Combinatorics.Claim4063

/-- A connected finite simple graph on at least one vertex has at least one
edge fewer than its number of vertices. -/
theorem connectedSimpleGraph_minEdges
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (_hV : 1 ≤ Fintype.card V) (hG : G.Connected) :
    Fintype.card V - 1 ≤ Nat.card G.edgeSet := by
  apply Nat.sub_le_iff_le_add'.mpr
  have h : Fintype.card V ≤ Nat.card G.edgeSet + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hG.card_vert_le_card_edgeSet_add_one
  simpa [Nat.add_comm] using h

end MathlibPlus.Combinatorics.Claim4063
