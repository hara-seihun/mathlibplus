import Mathlib.Tactic

namespace MathlibPlus.Arithmetic.Claim47930

/-! Exact arithmetic checks for the admitted R3548-S2 specialization. -/

/-- The target pair `(Ksq,c) = (14,10)` satisfies every displayed
admissibility check in the source packet. -/
theorem admissibilityChecks :
    (14 : ℤ) > 0 ∧
      (10 : ℤ) > 0 ∧
      5 * (14 : ℤ) ≥ 10 - 36 ∧
      (14 : ℤ) ≤ 3 * 10 ∧
      (12 : ℤ) ∣ 14 + 10 ∧
      (14 : ℤ) ≤ 2 * 10 := by
  norm_num

end MathlibPlus.Arithmetic.Claim47930
