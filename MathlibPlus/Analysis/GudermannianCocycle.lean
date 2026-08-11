import Mathlib

namespace MathlibPlus
namespace Analysis

/-- The antisymmetry and diagonal vanishing of the sine difference are
independent of any special property of the Gudermannian. -/
theorem gudermannianDifference_claim18004 (gd : ℝ → ℝ) :
    let D : ℝ → ℝ → ℝ := fun ξ₁ ξ₂ => Real.sin (gd ξ₁ - gd ξ₂)
    (∀ ξ₁ ξ₂, D ξ₂ ξ₁ = -D ξ₁ ξ₂) ∧ (∀ ξ, D ξ ξ = 0) := by
  dsimp
  constructor
  · intro ξ₁ ξ₂
    rw [show gd ξ₂ - gd ξ₁ = -(gd ξ₁ - gd ξ₂) by ring, Real.sin_neg]
  · intro ξ
    simp

end Analysis
end MathlibPlus
