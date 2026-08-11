import MathlibPlus.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.GraphTheory

/- Claim 31488: a spanning subgraph (same vertex type) cannot connect a
   graph that was disconnected. -/
theorem disconnected_spanning_subgraph_claim31488
    {V : Type*} {S T : SimpleGraph V} (hTS : T ≤ S) (hS : ¬ S.Connected) :
    ¬ T.Connected := by
  intro hT
  exact hS (hT.mono hTS)

/- Claim 31773: the complement of the vertical-line model has exactly the
   cross-line adjacency relation. -/
theorem complement_vertical_line_model_claim31773 (n : ℕ) :
    let V := Fin 7 × Fin n
    let G : SimpleGraph V := SimpleGraph.fromRel (fun x y => x.1 = y.1)
    ∀ x y : V, (Gᶜ).Adj x y ↔ x.1 ≠ y.1 := by
  dsimp
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hfst : x.1 = y.1
  · simp [SimpleGraph.fromRel_adj, hxy, hfst]
  · have hfst' : ¬ y.1 = x.1 := fun h => hfst h.symm
    simp [SimpleGraph.fromRel_adj, hxy, hfst, hfst']

end MathlibPlus.GraphTheory
