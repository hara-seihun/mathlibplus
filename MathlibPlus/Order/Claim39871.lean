import Mathlib.Order.Preorder.Finite

namespace MathlibPlus.Order

/-!
Formalization of admitted claim 39871.  The source's `Sup₂(G_R)` and
`≼_G` are not canonical Lean objects in the claim record, so this statement
exposes exactly their order-theoretic interface: a finite family `s`, its
partial order, and an element `X` of that family.
-/

/-- A finite partially ordered family has a minimal member below each member. -/
theorem existsMinimalBelowFinite_claim39871
    {α : Type*} [PartialOrder α] (s : Set α) (hs : s.Finite)
    {X : α} (hX : X ∈ s) :
    ∃ K ∈ s, K ≤ X ∧ ∀ L ∈ s, L ≤ X → L ≤ K → K ≤ L := by
  let t : Set α := s ∩ Set.Iic X
  have ht : t.Finite := hs.subset (by
    intro x hx
    exact hx.1)
  have htn : t.Nonempty := by
    exact ⟨X, ⟨hX, le_rfl⟩⟩
  obtain ⟨K, hKt, hKmin⟩ := ht.exists_minimal htn
  refine ⟨K, hKt.1, hKt.2, ?_⟩
  intro L hLs hLX hLK
  exact hKmin ⟨hLs, hLX⟩ hLK

end MathlibPlus.Order
