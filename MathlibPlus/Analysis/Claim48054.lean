import Mathlib

namespace MathlibPlus.Analysis

/-- Exact positioned majorant value in claim 48054.  The expectation and
load-law carrier are intentionally not reconstructed here; this is the exact
rational numerical conclusion displayed by the packet. -/
theorem claim48054_positioned_majorant_lt_two :
    (23 : ℚ) / 18 < 2 := by
  norm_num

/-- Exact comparison between the persistent-Plackett--Luce target area and the
positioned majorant in claim 48054. -/
theorem claim48054_target_area_lt_positioned_majorant :
    (61 : ℚ) / 72 < (23 : ℚ) / 18 := by
  norm_num

end MathlibPlus.Analysis
