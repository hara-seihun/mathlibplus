import Mathlib

namespace MathlibPlus.GroupTheory.Claim45659

/-- The coordinate degree `c + 2 * k` is injective on the stated finite ranges. -/
theorem r2999_DegreeInjective :
    ∀ c₁ c₂ : Fin 2, ∀ k₁ k₂ : Fin 4,
      c₁.1 + 2 * k₁.1 = c₂.1 + 2 * k₂.1 →
      c₁ = c₂ ∧ k₁ = k₂ := by
  intro c₁ c₂ k₁ k₂ h
  have hc : c₁.1 = c₂.1 := by omega
  have hk : k₁.1 = k₂.1 := by omega
  exact ⟨Fin.ext hc, Fin.ext hk⟩

end MathlibPlus.GroupTheory.Claim45659
