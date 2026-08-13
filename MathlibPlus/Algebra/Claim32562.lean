import Mathlib

namespace MathlibPlus.Algebra.Claim32562

/-- A normalized affine self-map of a commutative ring is linear. -/
theorem normalizedAffine_iff_linear
    {R : Type*} [CommRing R] (f : R → R) :
    (f 0 = 0 ∧ ∃ a b : R, ∀ x : R, f x = a * x + b) ↔
      ∃ a : R, ∀ x : R, f x = a * x := by
  constructor
  · rintro ⟨hzero, ⟨a, b, hab⟩⟩
    refine ⟨a, ?_⟩
    have hb : b = 0 := by
      have := hab 0
      simpa [hzero] using this.symm
    intro x
    rw [hab x, hb, add_zero]
  · rintro ⟨a, ha⟩
    refine ⟨?_, a, 0, ?_⟩
    · simpa [ha 0]
    · intro x
      rw [ha x]
      simp

/-- The nonzero normalized affine maps are exactly the nonzero linear maps. -/
theorem normalizedAffine_ne_zero_iff
    {R : Type*} [CommRing R] [Nontrivial R] (f : R → R) :
    ((f 0 = 0 ∧ ∃ a b : R, ∀ x : R, f x = a * x + b) ∧ f ≠ 0) ↔
      ∃ a : R, a ≠ 0 ∧ ∀ x : R, f x = a * x := by
  constructor
  · rintro ⟨haff, hf⟩
    rcases normalizedAffine_iff_linear f |>.mp haff with ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    intro hzero
    apply hf
    funext x
    rw [ha x, hzero]
    simp
  · rintro ⟨a, ha, hlin⟩
    refine ⟨normalizedAffine_iff_linear f |>.mpr ⟨a, hlin⟩, ?_⟩
    intro hzero
    have h_at_one := hlin 1
    rw [hzero] at h_at_one
    have ha_zero : a = 0 := by
      simpa using h_at_one.symm
    exact ha ha_zero

end MathlibPlus.Algebra.Claim32562
