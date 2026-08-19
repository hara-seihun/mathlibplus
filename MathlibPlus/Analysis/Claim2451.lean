import Mathlib

namespace MathlibPlus.Analysis.Claim2451

/-- The center-orthogonal line cancels the response when the two moments have
ratio `M₄ / M₂ = 5 / π`.  The moment carriers remain explicit parameters.
-/
theorem centerOrthogonalLine_cancel (α β M₂ M₄ : ℝ)
    (hM₂ : M₂ ≠ 0) (hRatio : M₄ / M₂ = 5 / Real.pi)
    (hβ : β = -(Real.pi / 5) * α) :
    α * M₂ + β * M₄ = 0 := by
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hRatio' := hRatio
  field_simp [hM₂, hπ] at hRatio'
  have hrel : M₂ * 5 = Real.pi * M₄ := by
    nlinarith [hRatio']
  rw [hβ]
  field_simp [hM₂, hπ]
  rw [hrel]
  ring

end MathlibPlus.Analysis.Claim2451
