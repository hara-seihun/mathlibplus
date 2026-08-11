import Mathlib

namespace MathlibPlus.Algebra.C13SectionSizes

/-- The explicit cardinality content of the `C₁₃` section-size claim, with a
section represented by its finite subset of `ZMod 13`. -/
theorem c13_section_size_bound_and_degeneracies (B : Finset (ZMod 13)) :
    B.card ≤ 13 ∧
      (B.card = 0 → B = ∅) ∧
      (B.card = 13 → B = Finset.univ) ∧
      (B.card = 11 → (Bᶜ).card = 2) ∧
      (B.card = 12 → (Bᶜ).card = 1) ∧
      (B.card = 0 → ∀ g h : ZMod 13,
        B.image (fun b => b + g) = B.image (fun b => b + h)) ∧
      (B.card = 13 → ∀ g h : ZMod 13,
        B.image (fun b => b + g) = B.image (fun b => b + h)) ∧
      (∀ g : ZMod 13,
        (B.image (fun b => b + g)).card = B.card) := by
  have hcard : B.card ≤ 13 := by
    have h := Finset.card_le_card (Finset.subset_univ B)
    simpa [ZMod.card] using h
  have hcomp : (Bᶜ).card = 13 - B.card := by
    simpa [ZMod.card] using Finset.card_compl B
  have htranslate (g : ZMod 13) :
      (B.image (fun b => b + g)).card = B.card := by
    exact Finset.card_image_of_injective B (add_left_injective g)
  have huniv_translate (g : ZMod 13) :
      (Finset.univ.image (fun b : ZMod 13 => b + g)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injective _ (add_left_injective g)]
    simp [ZMod.card]
  refine ⟨hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_eq_zero.mp
  · intro hB
    exact Finset.eq_univ_of_card B (by simpa [ZMod.card] using hB)
  · intro hB
    rw [hcomp, hB]
  · intro hB
    rw [hcomp, hB]
  · intro hB g h
    simp [Finset.card_eq_zero.mp hB]
  · intro hB g h
    rw [Finset.eq_univ_of_card B (by simpa [ZMod.card] using hB)]
    rw [huniv_translate g, huniv_translate h]
  · intro g
    exact htranslate g

end MathlibPlus.Algebra.C13SectionSizes
