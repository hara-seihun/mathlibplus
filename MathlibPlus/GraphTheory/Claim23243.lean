import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.GraphTheory.Claim23243

/-- In a connected finite simple graph, an edge is not a bridge exactly when it
lies on a cycle. -/
theorem nonbridge_iff_cycle_edge
    {V : Type*} [Fintype V] {G : SimpleGraph V} (_hG : G.Connected)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ¬ G.IsBridge e ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ e ∈ p.edges := by
  rw [SimpleGraph.isBridge_iff_forall_cycle_notMem he]
  push Not
  rfl

end MathlibPlus.GraphTheory.Claim23243
