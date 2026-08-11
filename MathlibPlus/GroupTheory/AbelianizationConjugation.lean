import Mathlib

namespace MathlibPlus.GroupTheory.AbelianizationConjugation

/-- Claim 24236: inner conjugation is invisible after passage to the
abelianization. -/
theorem innerConjugation_fixes_abelianization {A : Type*} [Group A]
    (a x : A) :
    Abelianization.of (a * x * a⁻¹) = Abelianization.of x := by
  simp [map_mul, mul_assoc]

/-- Claim 24236: the image in the abelianization is unchanged by conjugating
a subgroup. The left-hand set is the image of the explicitly displayed
conjugate set. -/
theorem abelianization_image_conjugate_subgroup {A : Type*} [Group A]
    (H : Subgroup A) (a : A) :
    {y : Abelianization A | ∃ x ∈ H, y = Abelianization.of (a * x * a⁻¹)} =
      {y : Abelianization A | ∃ x ∈ H, y = Abelianization.of x} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, innerConjugation_fixes_abelianization a x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (innerConjugation_fixes_abelianization a x).symm⟩

end MathlibPlus.GroupTheory.AbelianizationConjugation
