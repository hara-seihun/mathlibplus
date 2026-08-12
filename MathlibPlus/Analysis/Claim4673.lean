import Mathlib

namespace MathlibPlus.Analysis.Claim4673

/-- The shifted Laguerre parameter in the source convention. -/
noncomputable def shiftedLaguerreParameter (α : ℝ) : ℝ := α + 1 / 2

theorem shiftedLaguerreParameter_eq (α : ℝ) :
    shiftedLaguerreParameter α = α + 1 / 2 := by
  rfl

end MathlibPlus.Analysis.Claim4673
