import Mathlib

#check Nat.pow_le_pow_right
#check Nat.pow_le_pow_left
#check pow_le_pow_right'
#check pow_le_pow_right₀
#check Nat.one_le_pow
#check pow_le_pow_right₀

example (d : ℕ) : 27 ^ d ≠ 3^7 := by
  intro h
  by_cases hd : d ≤ 2
  · interval_cases d <;> norm_num at h
  · have hd3 : 3 ≤ d := by omega
    have hpow : 27 ^ 3 ≤ 27 ^ d := by
      exact Nat.pow_le_pow_right (by omega) hd3
    norm_num at hpow
    omega
