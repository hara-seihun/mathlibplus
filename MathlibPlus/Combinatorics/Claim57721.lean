import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MathlibPlus.Combinatorics.Claim57721

/-! The neighboring-degree multiset is an actual multiset, not a set, so
repeated neighbor degrees are counted with their multiplicities. -/

/-- The ordered degree / neighboring-degree profile of a vertex. -/
noncomputable def vertexType {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ × Multiset ℕ := by
  classical
  letI : Fintype ↑(G.neighborSet v) := Fintype.ofFinite _
  exact (G.degree v, (G.neighborFinset v).1.map (fun u =>
    letI : Fintype ↑(G.neighborSet u) := Fintype.ofFinite _
    G.degree u))

end MathlibPlus.Combinatorics.Claim57721
