import Mathlib

open scoped BigOperators

namespace MathlibPlus.GraphTheory.Claim24821

/-- The degree statistic attached to a vertex of a finite simple graph. -/
def rootDegree_claim24821 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : ℕ :=
  T.degree v

end MathlibPlus.GraphTheory.Claim24821

namespace MathlibPlus.GraphTheory.Claim24823

/-- The additive neighbor load attached to a vertex of a finite simple graph.

The source writes `N_v = ∑_{u ∼ v} (deg_T(u) - 1)`.  The finite-graph
carrier is explicit here; no tree, connectedness, or regularity hypothesis is
silently added to the definition.
-/
def additiveNeighborLoad_claim24823 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : ℕ :=
  (T.neighborFinset v).sum (fun u => T.degree u - 1)

end MathlibPlus.GraphTheory.Claim24823
