import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MathlibPlus.Combinatorics
open scoped Sym2

/-- The explicit order-eleven graph in claim 25033 is a tree. -/
theorem explicitOrderElevenTree_claim25033 :
    let E : Finset (Sym2 (Fin 11)) :=
      {s(0, 1), s(1, 2), s(2, 3), s(0, 6), s(6, 4),
       s(4, 5), s(5, 7), s(6, 8), s(7, 9), s(7, 10)}
    let G : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin 11)))
    G.IsTree := by
  dsimp
  let E : Finset (Sym2 (Fin 11)) :=
    {s(0, 1), s(1, 2), s(2, 3), s(0, 6), s(6, 4),
     s(4, 5), s(5, 7), s(6, 8), s(7, 9), s(7, 10)}
  let G : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin 11)))
  have h01 : G.Adj 0 1 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h12 : G.Adj 1 2 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h23 : G.Adj 2 3 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h06 : G.Adj 0 6 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h64 : G.Adj 6 4 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h45 : G.Adj 4 5 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h57 : G.Adj 5 7 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h68 : G.Adj 6 8 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h79 : G.Adj 7 9 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have h710 : G.Adj 7 10 := by
    simp only [G, SimpleGraph.fromEdgeSet_adj]
    native_decide
  have hconn : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro w
    fin_cases w
    · exact .rfl
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact h01.reachable.trans (h12.reachable.trans h23.reachable)
    · exact h06.reachable.trans h64.reachable
    · exact h06.reachable.trans (h64.reachable.trans h45.reachable)
    · exact h06.reachable
    · exact h06.reachable.trans (h64.reachable.trans (h45.reachable.trans h57.reachable))
    · exact h06.reachable.trans h68.reachable
    · exact h06.reachable.trans (h64.reachable.trans (h45.reachable.trans (h57.reachable.trans h79.reachable)))
    · exact h06.reachable.trans (h64.reachable.trans (h45.reachable.trans (h57.reachable.trans h710.reachable)))
  letI : Fintype G.edgeSet :=
    Fintype.ofFinset E (by
      intro e
      simp [G, E, SimpleGraph.edgeSet_fromEdgeSet]
      intro h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        native_decide)
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨hconn, ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  native_decide

end MathlibPlus.Combinatorics
