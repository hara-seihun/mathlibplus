import Mathlib

/-!
# Full-logarithmic reserve arithmetic

Exact scalar consequences extracted from source record `C-0178`.  The analytic
whole-strip estimate itself is not restated without its endpoint-kernel and transform
definitions.
-/

namespace MathlibPlus.Asymptotics.FullLogReserve

/-- The exponent in the packet's whole-strip estimate retains a power reserve below
`-1/2` at every fixed height strictly below `1/2`. -/
theorem stripExponent_lt_negHalf (Y : ℝ) (hY : Y < 1 / 2) :
    -5 / 4 + 3 * Y / 2 < -1 / 2 := by
  linarith

/-- On a positive scale, replacing `c` by `λ²` doubles its logarithm. -/
theorem log_sq (scale : ℝ) (hscale : 0 < scale) :
    Real.log (scale ^ 2) = 2 * Real.log scale := by
  rw [pow_two, Real.log_mul (ne_of_gt hscale) (ne_of_gt hscale)]
  ring

/-- Consequently the packet's support budget `A < log c` becomes
`A < 2 log λ` under the substitution `c = λ²`. -/
theorem support_lt_log_sq_iff (A scale : ℝ) (hscale : 0 < scale) :
    A < Real.log (scale ^ 2) ↔ A < 2 * Real.log scale := by
  rw [log_sq scale hscale]

end MathlibPlus.Asymptotics.FullLogReserve
