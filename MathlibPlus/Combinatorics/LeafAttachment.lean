import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 6434: the two ways to attach one leaf to `P₃` give `P₄` and `K_{1,3}`.

The old vertices are `0, 1, 2 : Fin 4`, the new leaf is `3`, and `r` is
its attachment vertex among the old three.  The first conclusion is stated
as a graph isomorphism because the endpoint attachment uses a different
ordering of the four vertices. -/
theorem leafAttachmentP3_claim6434 :
    let attachment : Fin 3 → SimpleGraph (Fin 4) := fun r =>
      SimpleGraph.fromRel (fun x y =>
        (x.val < 3 ∧ y.val < 3 ∧
            (x.val + 1 = y.val ∨ y.val + 1 = x.val)) ∨
          (x = 3 ∧ y.val = r.val))
    Nonempty (attachment 0 ≃g SimpleGraph.pathGraph 4) ∧
      attachment 1 = SimpleGraph.starGraph 1 := by
  dsimp
  constructor
  · have h :
        SimpleGraph.fromRel (fun x y : Fin 4 =>
          (x.val < 3 ∧ y.val < 3 ∧
              (x.val + 1 = y.val ∨ y.val + 1 = x.val)) ∨
            (x = 3 ∧ y.val = 0)) =
          (SimpleGraph.pathGraph 4).comap (finCycle 1) := by
      ext x y
      fin_cases x <;> fin_cases y <;>
        simp [SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
          SimpleGraph.comap_adj, finCycle_apply]
    rw [h]
    exact ⟨SimpleGraph.Iso.comap (finCycle 1) (SimpleGraph.pathGraph 4)⟩
  · ext x y
    fin_cases x <;> fin_cases y <;>
      simp [SimpleGraph.fromRel_adj, SimpleGraph.starGraph_adj]

end MathlibPlus.Combinatorics
