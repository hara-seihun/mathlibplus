import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40850: the exact displayed per-cutoff/per-block ratio and its
strict unit interval for rounding to 307,639,155. -/
def perCutoffPerBlockPriceRatio_claim40850 : Prop :=
  (3_999_309_011 : ℚ) / 13 = 307_639_154 + 9 / 13 ∧
    (307_639_154 : ℚ) < (3_999_309_011 : ℚ) / 13 ∧
      (3_999_309_011 : ℚ) / 13 < 307_639_155

end MathlibPlus.Open.Analysis
