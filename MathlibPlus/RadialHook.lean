import Mathlib

/-!
# Exact first radial-hook sign counterexample

Kernel-checked formalization of Record 16 from legacy packet `C-0025`. The result
certifies only the two displayed scalar signs. It is not registered as an obstruction
to an unresolved radial-hook hierarchy.
-/

namespace MathlibPlus.RadialHook

/-- At `L = log 2`, the packet's first principal quantity is positive while its
first one-hook quantity is negative. -/
theorem firstRadialHookCounterexample :
    let L := Real.log 2
    0 < (33 - 46 * L) / 121 ∧
      -(3 * (26 * L ^ 2 + 506 * L - 363)) / 2662 < 0 := by
  dsimp
  constructor
  · have hlogUpper : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hnum : 0 < 33 - 46 * Real.log 2 := by linarith
    exact div_pos hnum (by norm_num)
  · have hlogLower : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpoly : 0 < 26 * (Real.log 2) ^ 2 + 506 * Real.log 2 - 363 := by
      nlinarith
    have hnum : -(3 * (26 * (Real.log 2) ^ 2 + 506 * Real.log 2 - 363)) < 0 := by
      nlinarith
    exact div_neg_of_neg_of_pos hnum (by norm_num)

end MathlibPlus.RadialHook
