import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0276

/-- The canonical `[0,2)` odd vector from the admitted claim. -/
def canonicalOddVector (h₀ h₂ : ℝ) : ℝ × ℝ :=
  (Real.sqrt (h₀ * h₂), -Real.sqrt (h₀ * h₂))

/-- The displayed canonical odd vector is nonzero whenever `h₀ h₂ > 0`. -/
def canonicalOddChannelNonzero : Prop :=
  ∀ h₀ h₂ : ℝ,
    0 < h₀ * h₂ →
      canonicalOddVector h₀ h₂ ≠ ((0, 0) : ℝ × ℝ)

end MathlibPlus.Open.ResearchFormalization.R0276
