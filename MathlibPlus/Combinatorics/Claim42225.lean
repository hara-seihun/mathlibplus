import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 42225: traces over a member of a finite union-closed family are closed
under union when the corresponding outside supports are unioned. -/
theorem outsideTraceFiberProduct_claim42225
    {α : Type*}
    (F : Set (Set α)) (hFfinite : F.Finite)
    (hUnion : ∀ ⦃A B : Set α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (M : Set α) (hM : M ∈ F)
    (S T X Y : Set α) :
    let H : Set α → Set (Set α) :=
      fun U => {Z | ∃ A ∈ F, A \ M = U ∧ A ∩ M = Z}
    H S X → H T Y → H (S ∪ T) (X ∪ Y) := by
  dsimp
  intro hX hY
  obtain ⟨A, hAF, hAout, hAtr⟩ := hX
  obtain ⟨B, hBF, hBout, hBtr⟩ := hY
  refine ⟨A ∪ B, hUnion hAF hBF, ?_, ?_⟩
  · rw [Set.union_sdiff_distrib, hAout, hBout]
  · rw [Set.union_inter_distrib_right, hAtr, hBtr]

end MathlibPlus.Combinatorics
