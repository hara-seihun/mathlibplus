import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card

namespace MathlibPlus.GraphTheory.Claim23400

/-- The induced graph after deleting `v` has a finite vertex type and one fewer
vertex.  Simplicity is intrinsic to `SimpleGraph`, so `G.induce` supplies the
simple graph in the claim. -/
theorem delete_vertex_finite_simple_order_claim23400
    {V : Type*} [Finite V] (G : SimpleGraph V) (v : V) :
    ∃ G' : SimpleGraph (↥(Set.univ \ ({v} : Set V))),
      G' = G.induce (Set.univ \ ({v} : Set V)) ∧
        Finite (↥(Set.univ \ ({v} : Set V))) ∧
          Nat.card (↥(Set.univ \ ({v} : Set V))) = Nat.card V - 1 := by
  refine ⟨G.induce (Set.univ \ ({v} : Set V)), rfl, ?_⟩
  constructor
  · infer_instance
  · rw [Nat.card_coe_set_eq]
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ v)]
    simp

end MathlibPlus.GraphTheory.Claim23400
