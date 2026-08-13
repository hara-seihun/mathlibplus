import Mathlib

namespace MathlibPlus.Combinatorics.Claim29506

/-- The concrete three-part cycle blow-up is the complete tripartite graph.
The source packet's `RCC` notation is represented here by its displayed vertex
set and adjacency relation; no separate graph-family definition is introduced.
-/
theorem rccThree_is_completeMultipartite_claim29506 (n : ℕ) (_hn : 2 ≤ n) :
    Nonempty (
      SimpleGraph.fromRel (fun x y : Fin 3 × Fin n => x.1 ≠ y.1) ≃g
        SimpleGraph.completeMultipartiteGraph (fun _ : Fin 3 => Fin n)) := by
  let e : (Fin 3 × Fin n) ≃ Σ _ : Fin 3, Fin n :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.1, x.2)
      left_inv := by intro x; rfl
      right_inv := by intro x; cases x; rfl }
  refine ⟨⟨e, ?_⟩⟩
  intro x y
  simp only [SimpleGraph.fromRel_adj, SimpleGraph.completeMultipartiteGraph,
    SimpleGraph.comap_adj, Function.Embedding.coe_subtype, Equiv.coe_fn_mk,
    e]
  constructor
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hxy
    exact h (congrArg Prod.fst hxy)
  · rintro ⟨_, h | h⟩
    · exact h
    · intro hxy
      exact h hxy.symm

end MathlibPlus.Combinatorics.Claim29506
