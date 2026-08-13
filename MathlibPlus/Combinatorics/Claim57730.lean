import Mathlib

namespace MathlibPlus.Combinatorics.Claim57730

/-- A vertex is universal in a simple graph exactly when it is isolated in
its complement.  This is the vertex-wise claim; it does not assert that a
disconnected complement has an isolated vertex. -/
theorem universal_iff_isolated_complement_claim57730
    {V : Type*} (G : SimpleGraph V) (v : V) :
    G.IsUniversal v ↔ Gᶜ.IsIsolated v := by
  exact (SimpleGraph.isIsolated_compl_iff_isUniversal (G := G) (v := v)).symm

end MathlibPlus.Combinatorics.Claim57730
