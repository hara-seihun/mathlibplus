import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

open scoped SimpleGraph

namespace MathlibPlus.GraphTheory

theorem compl_induce_deleteVertex
    {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) :
    Nonempty (Gᶜ.induce (Set.univ \ {v}) ≃g
      (G.induce (Set.univ \ {v}))ᶜ) := by
  classical
  have h : Gᶜ.induce (Set.univ \ {v}) =
      (G.induce (Set.univ \ {v}))ᶜ := by
    ext x y
    change (x.val ≠ y.val ∧ ¬ G.Adj x.val y.val) ↔
      (x ≠ y ∧ ¬ G.Adj x.val y.val)
    constructor
    · rintro ⟨hxy, hG⟩
      exact ⟨fun h => hxy (congrArg Subtype.val h), hG⟩
    · rintro ⟨hxy, hG⟩
      exact ⟨fun h => hxy (Subtype.ext h), hG⟩
  rw [h]
  exact ⟨SimpleGraph.Iso.refl⟩

theorem compl_induce_deleteVertex_card
    {V : Type*} [Finite V]
    (v : V) :
    Nat.card (↥(Set.univ \ ({v} : Set V))) = Nat.card V - 1 := by
  classical
  letI := Fintype.ofFinite V
  have hcomp := Fintype.card_subtype_compl (fun x : V => x = v)
  have hsingle := Fintype.card_subtype_eq v
  simpa [Nat.card_eq_fintype_card, Set.mem_diff, Set.mem_univ, hsingle] using hcomp

end MathlibPlus.GraphTheory
