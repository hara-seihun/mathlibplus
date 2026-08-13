import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 17625: the first vertical ladder source is the displayed linear
three-variable form. -/
theorem vertical_ladder_entrance_source_claim17625
    (x y z : ℝ) :
    (2 / 3 : ℝ) * (x + y + z) =
      (2 / 3 : ℝ) * x + (2 / 3 : ℝ) * y + (2 / 3 : ℝ) * z := by
  ring

end MathlibPlus.Analysis
