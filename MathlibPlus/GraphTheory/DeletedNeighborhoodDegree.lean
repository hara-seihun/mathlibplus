import Mathlib

namespace MathlibPlus.GraphTheory

/-- Deleting a vertex from a finite regular simple graph lowers the degree of
exactly its former neighbors by one.  The punctured degree is written as the
cardinality of the original neighbor set with the deleted vertex removed. -/
theorem deletedNeighborhoodDegree
    {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ)
    (hreg : ∀ w : V, (F.neighborSet w).ncard = d)
    {u v : V} (_hv : v ≠ u) :
    (F.neighborSet v \ {u}).ncard =
      if F.Adj v u then d - 1 else d := by
  classical
  by_cases huv : F.Adj v u
  · have hsubset : ({u} : Set V) ⊆ F.neighborSet v := by
      rw [Set.singleton_subset_iff]
      exact (F.mem_neighborSet v u).mpr huv
    rw [if_pos huv, Set.ncard_sdiff hsubset, Set.ncard_singleton,
      hreg v]
  · have hset : F.neighborSet v \ {u} = F.neighborSet v := by
      ext w
      constructor
      · intro hw
        exact hw.1
      · intro hw
        refine ⟨hw, ?_⟩
        intro hwu
        apply huv
        have hwu' : w = u := Set.mem_singleton_iff.mp hwu
        subst w
        exact (F.mem_neighborSet v u).mp hw
    rw [if_neg huv, hset, hreg v]

end MathlibPlus.GraphTheory
