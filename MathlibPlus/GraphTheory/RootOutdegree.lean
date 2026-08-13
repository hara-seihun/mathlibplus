import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MathlibPlus.GraphTheory

/-- Admitted claim 5596 in an explicit finite-simple-graph interface.  `B` is
represented by the branch-root adjacency at `ri`: it contains exactly the
neighbors of `ri` in `C` other than the reattached parent `v`. -/
theorem rootOutdegree_after_parent_claim5596
    {V : Type*} [Fintype V] (C B : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel B.Adj]
    (v ri : V) (h_parent : C.Adj v ri)
    (h_branch : ∀ w : V, B.Adj ri w ↔ C.Adj ri w ∧ w ≠ v) :
    B.degree ri = C.degree ri - 1 := by
  classical
  have hmem : v ∈ C.neighborFinset ri := by
    rw [C.mem_neighborFinset]
    exact (C.adj_comm v ri).mp h_parent
  have hfin : B.neighborFinset ri = (C.neighborFinset ri).erase v := by
    ext w
    rw [B.mem_neighborFinset, Finset.mem_erase, C.mem_neighborFinset]
    constructor
    · intro h
      have h' := (h_branch w).mp h
      exact ⟨h'.2, h'.1⟩
    · intro h
      apply (h_branch w).mpr
      exact ⟨h.2, h.1⟩
  change (B.neighborFinset ri).card = (C.neighborFinset ri).card - 1
  rw [hfin, Finset.card_erase_of_mem hmem]

end MathlibPlus.GraphTheory
