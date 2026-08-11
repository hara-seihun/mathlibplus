import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MathlibPlus.Combinatorics

/-!
Formalization of admitted claim 23404 in Mathlib's finite simple-graph model.
The finite vertex type and decidable adjacency give the packet's finite edge set.
-/

/-- The sum of finite simple-graph vertex degrees is twice the edge count. -/
theorem handshakeDegreeSum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  simpa using G.sum_degrees_eq_twice_card_edges

end MathlibPlus.Combinatorics
