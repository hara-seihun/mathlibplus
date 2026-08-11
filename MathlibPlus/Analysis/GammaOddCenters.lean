import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MathlibPlus.Analysis.GammaOddCenters

/-- Claim 42866: cosine vanishes at every positive odd half-period. -/
theorem cosine_odd_half (n : ℕ) :
    Real.cos (Real.pi * (2 * (n : ℝ) + 1) / 2) = 0 := by
  have h := Real.cos_add_nat_mul_pi (Real.pi / 2) n
  rw [Real.cos_pi_div_two, mul_zero] at h
  have heq : Real.pi * (2 * (n : ℝ) + 1) / 2 =
      Real.pi / 2 + (n : ℝ) * Real.pi := by ring
  rw [heq]
  exact h

/-- Claim 42867: the reflected half of an odd center is the negative integer. -/
theorem reflected_half (n : ℕ) :
    (1 - (2 * (n : ℝ) + 1)) / 2 = -(n : ℝ) := by ring

/-- Claim 42869: the positive half of an odd center is the next integer. -/
theorem positive_half (n : ℕ) :
    (1 + (2 * (n : ℝ) + 1)) / 2 = (n : ℝ) + 1 := by ring

end MathlibPlus.Analysis.GammaOddCenters
