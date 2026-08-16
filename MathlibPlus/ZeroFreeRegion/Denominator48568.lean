import Mathlib

/-!
# Exact zero-free-region denominator improvement to 4.8568

This file formalizes the standalone arithmetic in Record 4 of source record
`C-0096`. It does not assert the packet's analytic Riemann-zeta zero-free region.
-/

namespace MathlibPlus.ZeroFreeRegion

/-- Replacing denominator `4.8594` by `4.8568` decreases it by exactly `13/5000`
and increases its reciprocal amplitude by exactly `1250/11346699`; relative to
`4.862`, the denominator decrease is `13/2500`. -/
theorem denominator48568Improvement :
    (4.8594 : ℝ) - 4.8568 = 13 / 5000 ∧
    (0 : ℝ) < 13 / 5000 ∧
    (1 / 4.8568 : ℝ) - 1 / 4.8594 = 1250 / 11346699 ∧
    (0 : ℝ) < 1250 / 11346699 ∧
    (4.862 : ℝ) - 4.8568 = 13 / 2500 := by
  norm_num

end MathlibPlus.ZeroFreeRegion
