import Mathlib

/-!
# Prime digit-sum threshold arithmetic

This file formalizes the exact threshold comparison in Record 2 of legacy packet
`C-0092`. It makes no claim that either threshold is least or optimal, and it does
not import the packet's analytic prime-existence argument.
-/

namespace MathlibPlus.PrimeDigitSum

/-- The old sufficient prime digit-sum threshold exceeds the packet's new sufficient
threshold by exactly `39809603683661578781640732352491`, a relative decrease strictly
between the two stated decimal bounds. -/
theorem exactThresholdDecrease :
    (177843590339381623423137292296355 : ℕ) -
        138033986655720044641496559943864 =
      39809603683661578781640732352491 ∧
    (177843590339381623423137292296355 : ℝ) -
        138033986655720044641496559943864 =
      39809603683661578781640732352491 ∧
    ((177843590339381623423137292296355 : ℝ) -
          138033986655720044641496559943864) /
          177843590339381623423137292296355 * 100 >
      22.38461538461538 ∧
    ((177843590339381623423137292296355 : ℝ) -
          138033986655720044641496559943864) /
          177843590339381623423137292296355 * 100 <
      22.38461538461539 := by
  norm_num

end MathlibPlus.PrimeDigitSum
