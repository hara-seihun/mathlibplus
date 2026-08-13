import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 1553: the printed final amplitude comparison is false.  The
terminating decimals are interpreted exactly by Lean's decimal notation. -/
theorem falseFinalAmplitudeComparison_claim1553 :
    ¬ ((0.01945 : ℝ) > 1 / 51.34) := by
  norm_num

end MathlibPlus.Analysis
