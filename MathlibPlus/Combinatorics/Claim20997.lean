import Mathlib

namespace MathlibPlus.Combinatorics.Claim20997

/--
The exact singleton-fibre reconstruction in claim 20997.  The family `β` is
left as the source-level interface: `Ai` and `Aj` are its fibres at the two
distinct colors, and `Pij` is their pairwise-union product.  No finiteness or
extra structure is needed for this intersection identity.
-/
theorem singletonFiberIntersectionReconstruction
    {X : Type*} (β : Set X → Set (Set X)) (ti tj : X)
    (_hij : ti ≠ tj)
    (h_empty : ⋂ B : β {tj}, (B : Set X) = ∅) :
    let Ai := β {ti}
    let Aj := β {tj}
    let Pij : Set (Set X) :=
      {C | ∃ A ∈ Ai, ∃ B ∈ Aj, C = A ∪ (B : Set X)}
    (∀ A ∈ Ai, A = ⋂ B : Aj, A ∪ (B : Set X)) ∧
      (∀ A ∈ Ai, ∀ B : Aj, A ∪ (B : Set X) ∈ Pij) := by
  dsimp
  constructor
  · intro A hA
    ext x
    constructor
    · intro hxA
      exact Set.mem_iInter.2 fun B => Set.mem_union_left _ hxA
    · intro hxInter
      by_contra hxA
      have hxNot : x ∉ ⋂ B : β {tj}, (B : Set X) := by
        rw [h_empty]
        simp
      have hex : ∃ B : β {tj}, x ∉ (B : Set X) := by
        simpa only [Set.mem_iInter, not_forall] using hxNot
      obtain ⟨B, hB⟩ := hex
      have hxUnion := Set.mem_iInter.1 hxInter B
      exact hB (hxUnion.resolve_left hxA)
  · intro A hA B
    exact ⟨A, hA, (B : Set X), B.property, rfl⟩

end MathlibPlus.Combinatorics.Claim20997
