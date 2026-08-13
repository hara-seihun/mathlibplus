import Mathlib

namespace MathlibPlus.Algebra.Claim50313

/-- The explicit residual from claim 50313 vanishes at `n = 21` and is
negative at `n = 22`, where it equals `-63/30976`. -/
theorem residual_evaluation_claim50313 :
    let R : ℚ → ℚ := fun n => 3 * (n - 1) * (21 - n) / (64 * n ^ 2)
    R 21 = 0 ∧ R 22 = -63 / 30976 ∧ R 22 < 0 := by
  norm_num

end MathlibPlus.Algebra.Claim50313
