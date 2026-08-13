import Mathlib

namespace MathlibPlus.Combinatorics

/-- The section-cardinality implication from claim 57666.  The section over
`a` is written out in the statement, so no auxiliary quotient definition or
unstated regularity hypothesis is introduced. -/
theorem sectionCardinalityObstruction_claim57666
    {A B : Type*} [Fintype A] [Fintype B]
    (S T : Set (A × B))
    (htransport : ∃ α : A ≃ A, ∃ β : B ≃ B,
      ∀ a : A,
        β '' {b : B | (a, b) ∈ S} =
          {b : B | (α a, b) ∈ T}) :
    ∃ α : A ≃ A, ∀ a : A,
      Set.ncard {b : B | (a, b) ∈ S} =
        Set.ncard {b : B | (α a, b) ∈ T} := by
  rcases htransport with ⟨α, β, hαβ⟩
  refine ⟨α, ?_⟩
  intro a
  have hcard :=
    Set.ncard_image_of_injective {b : B | (a, b) ∈ S} β.injective
  rw [hαβ a] at hcard
  exact hcard.symm

/-- The contrapositive section-cardinality obstruction from claim 57666. -/
theorem sectionCardinalityObstruction_noTransporter_claim57666
    {A B : Type*} [Fintype A] [Fintype B]
    (S T : Set (A × B))
    (hsize : ∀ α : A ≃ A, ∃ a : A,
      Set.ncard {b : B | (a, b) ∈ S} ≠
        Set.ncard {b : B | (α a, b) ∈ T}) :
    ¬ ∃ α : A ≃ A, ∃ β : B ≃ B,
      ∀ a : A,
        β '' {b : B | (a, b) ∈ S} =
          {b : B | (α a, b) ∈ T} := by
  rintro ⟨α, β, hαβ⟩
  obtain ⟨a, ha⟩ := hsize α
  have hcard : Set.ncard {b : B | (a, b) ∈ S} =
      Set.ncard {b : B | (α a, b) ∈ T} := by
    have himage :=
      Set.ncard_image_of_injective {b : B | (a, b) ∈ S} β.injective
    rw [hαβ a] at himage
    exact himage.symm
  exact ha hcard

end MathlibPlus.Combinatorics
