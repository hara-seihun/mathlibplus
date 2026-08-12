import Mathlib

namespace MathlibPlus.Analysis.Claim22041

/-- Pointwise lower bound for the carrier `T²` block in admitted claim 22041.
The unit-modulus condition on `ω` is made explicit because it is the phase
hypothesis needed for the displayed inequality. -/
theorem carrierT2Block_lower_bound (c : ℝ) (b ω T : ℂ) (hω : ‖ω‖ = 1) :
    c * ‖T‖ ^ 2 - Complex.re (ω ^ 2 * b * T ^ 2) ≥
      (c - ‖b‖) * ‖T‖ ^ 2 := by
  have hRe : Complex.re (ω ^ 2 * b * T ^ 2) ≤ ‖ω ^ 2 * b * T ^ 2‖ :=
    Complex.re_le_norm _
  have hnorm : ‖ω ^ 2 * b * T ^ 2‖ = ‖b‖ * ‖T‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hω]
    norm_num
  rw [hnorm] at hRe
  linarith

/-- Positive reserve follows from the lower bound when `c - ‖b‖` is bounded
below by a positive constant. -/
theorem carrierT2Block_nonnegative (c B₀ : ℝ) (b ω T : ℂ)
    (hω : ‖ω‖ = 1) (hB : B₀ ≤ c - ‖b‖) (hBpos : 0 < B₀) :
    0 ≤ c * ‖T‖ ^ 2 - Complex.re (ω ^ 2 * b * T ^ 2) := by
  have hlower := carrierT2Block_lower_bound c b ω T hω
  have hrhs : 0 ≤ (c - ‖b‖) * ‖T‖ ^ 2 := by
    exact mul_nonneg (le_trans (le_of_lt hBpos) hB) (sq_nonneg _)
  linarith

end MathlibPlus.Analysis.Claim22041
