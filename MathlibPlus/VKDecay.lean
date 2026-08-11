import Mathlib

/-!
# Vinogradov--Korobov decay comparisons

Exact coefficient arithmetic extracted from legacy packet `C-0093`.
-/

namespace MathlibPlus.VKDecay

/-- The exact improvements represented by the historical target coefficient
`0.2043672` over the baseline `0.1853` and the surviving coefficient `0.2043`. -/
theorem decayDeltas :
    (0.2043672 : ℝ) - 0.1853 = 11917 / 625000 ∧
    (0.2043672 : ℝ) - 0.2043 = 42 / 625000 := by
  norm_num

end MathlibPlus.VKDecay
