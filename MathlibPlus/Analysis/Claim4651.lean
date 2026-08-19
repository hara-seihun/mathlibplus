import Mathlib

namespace MathlibPlus.Analysis.Claim4651

/-- The affine family `H_c(w) = c + 2 (w - 1/4) A(w)` differs from its
physical member at `c = 1/2` by the constant `c - 1/2`. -/
theorem affine_constant_shift (A : ℝ → ℝ) (c w : ℝ) :
    (c + 2 * (w - (1 : ℝ) / 4) * A w) =
      ((1 : ℝ) / 2 + 2 * (w - (1 : ℝ) / 4) * A w) +
        (c - (1 : ℝ) / 2) := by
  ring

end MathlibPlus.Analysis.Claim4651
