import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- Cancellation of a common nonzero factor in two multiplicative state
coordinates, with the three-state equalities made explicit. -/
theorem claim26873_common_factor_cancel
    {G : Type*} [CommGroupWithZero G]
    {H p₁ p₂ p₃ ν₁ ν₂ ν₃ : G} (hH : H ≠ 0)
    (hp : H * p₁ = H * p₂ ∧ H * p₂ = H * p₃)
    (hν : H * ν₁ = H * ν₂ ∧ H * ν₂ = H * ν₃) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ ν₁ = ν₂ ∧ ν₂ = ν₃ := by
  have hp₁₂ : p₁ = p₂ := by exact mul_left_cancel₀ hH hp.1
  have hp₂₃ : p₂ = p₃ := by exact mul_left_cancel₀ hH hp.2
  have hν₁₂ : ν₁ = ν₂ := by exact mul_left_cancel₀ hH hν.1
  have hν₂₃ : ν₂ = ν₃ := by exact mul_left_cancel₀ hH hν.2
  exact ⟨hp₁₂, hp₂₃, hν₁₂, hν₂₃⟩

end MathlibPlus.Algebra
