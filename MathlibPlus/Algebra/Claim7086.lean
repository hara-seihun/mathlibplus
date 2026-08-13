import Mathlib

namespace MathlibPlus.Algebra.Claim7086

/-- The coordinate null-cone content of admitted claim 7086: the two-by-two
 determinant quadric is exactly the rank-one tensor cone. -/
theorem determinantQuadricSegreNullCone_claim7086 :
    ∀ (K : Type*) [Field K] (a b c d : K),
      a * d - b * c = 0 ↔
        ∃ u₀ u₁ v₀ v₁ : K,
          a = u₀ * v₀ ∧ b = u₀ * v₁ ∧ c = u₁ * v₀ ∧ d = u₁ * v₁ := by
  intro K _ a b c d
  constructor
  · intro h
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · refine ⟨0, 1, c, d, ?_⟩
        simp [ha, hb]
      · have hbc : b * c = 0 := by
          apply neg_eq_zero.mp
          simpa [ha] using h
        have hc : c = 0 := (mul_eq_zero.mp hbc).resolve_left hb
        refine ⟨b, d, 0, 1, ?_⟩
        simp [ha, hc]
    · refine ⟨a, c, 1, b / a, ?_⟩
      constructor
      · simp
      constructor
      · field_simp
      constructor
      · simp
      · field_simp [ha]
        linear_combination h
  · rintro ⟨u₀, u₁, v₀, v₁, rfl, rfl, rfl, rfl⟩
    ring

end MathlibPlus.Algebra.Claim7086
