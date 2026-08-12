import Mathlib

namespace MathlibPlus.Analysis.Claim42870

/-- The sine value at every positive odd half-period is nonzero. -/
theorem oddHalfPeriod_sine_ne_zero_claim42870 (n : ℕ) :
    Real.sin (Real.pi * ((2 * n + 1 : ℕ) : ℝ) / 2) ≠ 0 := by
  rw [show Real.pi * ((2 * n + 1 : ℕ) : ℝ) / 2 =
      Real.pi / 2 + (n : ℝ) * Real.pi by
    push_cast
    ring]
  rw [Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  simp

end MathlibPlus.Analysis.Claim42870
