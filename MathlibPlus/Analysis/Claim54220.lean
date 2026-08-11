import Mathlib

namespace MathlibPlus
namespace Analysis

/-- Exact rational arithmetic in the proportional-allocation counterexample;
the source-specific λ, recursion, and law carriers are intentionally external. -/
theorem proportional_allocation_gap_arithmetic_claim54220 :
    (393 / 512 : ℚ) - 4223 / 43008 = 28789 / 43008 ∧
    (28789 / 43008 : ℚ) > 0 ∧
    (-4125 / 8192 : ℚ) < 0 := by
  norm_num

end Analysis
end MathlibPlus
