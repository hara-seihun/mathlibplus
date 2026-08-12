import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim11729

/--
The standard order-eight model of `W(C₂)` is `DihedralGroup 4`.  In the
reflection generators `sr 0` and `sr 1`, every one-dimensional character
has trivial image on the longest element `(s₀ s₁)²`.
-/
theorem longestImage_eq_one
    {G : Type*} [CommGroup G]
    (χ : DihedralGroup 4 →* G) :
    χ ((DihedralGroup.sr 0 * DihedralGroup.sr 1) ^ 2) = 1 := by
  have h0 : (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
  have h1 : (DihedralGroup.sr 1 : DihedralGroup 4) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
  calc
    χ ((DihedralGroup.sr 0 * DihedralGroup.sr 1) ^ 2) =
        χ (DihedralGroup.sr 0 * DihedralGroup.sr 1) ^ 2 := map_pow χ _ 2
    _ = (χ (DihedralGroup.sr 0) * χ (DihedralGroup.sr 1)) ^ 2 := by rw [map_mul]
    _ = χ (DihedralGroup.sr 0) ^ 2 * χ (DihedralGroup.sr 1) ^ 2 := by rw [mul_pow]
    _ = χ ((DihedralGroup.sr 0 : DihedralGroup 4) ^ 2) *
        χ ((DihedralGroup.sr 1 : DihedralGroup 4) ^ 2) := by
      rw [map_pow, map_pow]
    _ = 1 := by rw [h0, h1]; simp

/-- The stabilizer sign `η(w₀) = -1` cannot extend to a one-dimensional
character of the order-eight Weyl group. -/
theorem noOneDimensionalCharacterWithNegativeLongest
    (χ : DihedralGroup 4 →* ℂˣ)
    (hχ : χ ((DihedralGroup.sr 0 * DihedralGroup.sr 1) ^ 2) = (-1 : ℂˣ)) :
    False := by
  have hw := longestImage_eq_one χ
  have hunit : (1 : ℂˣ) = (-1 : ℂˣ) := hw.symm.trans hχ
  have hcomplex : (1 : ℂ) = -1 := congrArg (fun z : ℂˣ => (z : ℂ)) hunit
  norm_num at hcomplex

/-- Existential form of the non-extension statement. -/
theorem noOneDimensionalWeylCharacter
    : ¬ ∃ χ : DihedralGroup 4 →* ℂˣ,
        χ ((DihedralGroup.sr 0 * DihedralGroup.sr 1) ^ 2) = (-1 : ℂˣ) := by
  rintro ⟨χ, hχ⟩
  exact noOneDimensionalCharacterWithNegativeLongest χ hχ

end MathlibPlus.GroupTheory.Claim11729
