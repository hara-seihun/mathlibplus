import Mathlib

namespace MathlibPlus.Analysis

/-- Exact rational interpretation of the FKS table-envelope coefficient,
including both printed decimal forms. -/
theorem fksTableEnvelopeCoefficient :
    (28681317 : ℝ) / 2000000000 = 143406585 / 10000000000 ∧
      (28681317 : ℝ) / 2000000000 =
        ((15485 : ℝ) / 10000) * (1 / 10 ^ 12) * 2100 ^ 3 ∧
      0 < (28681317 : ℝ) / 2000000000 := by
  norm_num

end MathlibPlus.Analysis
