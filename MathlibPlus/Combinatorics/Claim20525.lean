import Mathlib

namespace MathlibPlus.Combinatorics.Claim20525

/--
The collision shadow keeps precisely the members of `F` that remain after
removing the coordinate `y` and whose y-extension is also in `F`.  The ground
set is represented by `Set.univ`, so the source condition `A ⊆ X \ {y}` is
written literally.
-/
theorem collisionShadow_unionClosed
    {α : Type*} (F : Set (Set α))
    (hF : ∀ ⦃A B : Set α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F) (y : α) :
    ∀ ⦃A B : Set α⦄,
      (A ⊆ (Set.univ : Set α) \ {y} ∧ A ∈ F ∧ A ∪ {y} ∈ F) →
      (B ⊆ (Set.univ : Set α) \ {y} ∧ B ∈ F ∧ B ∪ {y} ∈ F) →
      (A ∪ B ⊆ (Set.univ : Set α) \ {y} ∧
        A ∪ B ∈ F ∧ (A ∪ B) ∪ {y} ∈ F) := by
  intro A B hA hB
  rcases hA with ⟨hAsub, hAF, hAyF⟩
  rcases hB with ⟨hBsub, hBF, hByF⟩
  have hsub : A ∪ B ⊆ (Set.univ : Set α) \ {y} := by
    intro x hx
    rcases hx with hxA | hxB
    · exact hAsub hxA
    · exact hBsub hxB
  have hAB : A ∪ B ∈ F := hF hAF hBF
  have hABY : (A ∪ {y}) ∪ (B ∪ {y}) ∈ F := hF hAyF hByF
  refine ⟨hsub, hAB, ?_⟩
  simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hABY

end MathlibPlus.Combinatorics.Claim20525
