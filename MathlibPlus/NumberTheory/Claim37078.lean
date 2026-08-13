import Mathlib

namespace MathlibPlus.NumberTheory

/-- Claim 37078: the strict prime-square inequalities used by the
row-dependent characteristic-prime schedule. -/
theorem claim37078_strictInequalities :
    (∀ p : ℕ, Nat.Prime p → 5 ≤ p → 3 * p < p ^ 2) ∧
      21 < 7 ^ 2 ∧
      35 < 7 ^ 2 ∧
      (∀ p : ℕ, Nat.Prime p → 11 ≤ p → 7 * p < p ^ 2) := by
  constructor
  · intro p hp h5
    have h3 : 3 < p := by omega
    have hp0 : 0 < p := by omega
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_right h3 hp0
  constructor
  · norm_num
  constructor
  · norm_num
  · intro p hp h11
    have h7 : 7 < p := by omega
    have hp0 : 0 < p := by omega
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_right h7 hp0

end MathlibPlus.NumberTheory
