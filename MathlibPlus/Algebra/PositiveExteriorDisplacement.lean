import Mathlib

namespace MathlibPlus.Algebra

/-- The positive cubic displacement correction from the source is strictly
positive whenever both displacement parameters are positive. -/
theorem positiveExteriorDisplacementGain {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    0 < δ ^ 3 + (4 + 2 * r) * δ ^ 2 + (8 * r + r ^ 2) * δ := by
  positivity

end MathlibPlus.Algebra
