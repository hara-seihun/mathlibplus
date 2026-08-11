import Mathlib

namespace MathlibPlus.Arithmetic

/-- The exact byte counts in the stated float-float vector storage calculation. -/
theorem floatFloatVector_storage_arithmetic_claim42721 :
    (2 ^ 26 : ℕ) = 67108864 ∧
      (2 ^ 26 : ℕ) * 16 = 2 ^ 30 ∧
      (2 ^ 30 : ℕ) = 1073741824 ∧
      2 * ((2 ^ 26 : ℕ) * 16) = 2 ^ 31 ∧
      (2 ^ 31 : ℕ) = 2147483648 := by
  norm_num

end MathlibPlus.Arithmetic
