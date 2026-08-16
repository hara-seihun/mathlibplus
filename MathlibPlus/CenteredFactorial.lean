import Mathlib

/-!
# Centered factorial determinant certificates

A kernel-checked scalar certificate extracted from source record `C-0038`.
This module formalizes the packet's exact radical inequality; it does not replace
that packet's separate reciprocal-zero or entire-function statements.
-/

namespace MathlibPlus.CenteredFactorial

/-- The exact negative value certificate used by the packet's `θ = π / 5`,
`t = 10` centered-factorial `D₃` witness. -/
theorem explicitFactorialD3NegativeWitness :
    (2604 : ℝ) - 2000 * Real.sqrt 5 < 0 := by
  have hs : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg 5
  have hs_sq : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by norm_num
  nlinarith

end MathlibPlus.CenteredFactorial
