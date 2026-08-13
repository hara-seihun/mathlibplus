import Mathlib

namespace MathlibPlus.Combinatorics

/-!
# Quadratic binomial degree decrement

Claim 20155 uses the elementary difference of consecutive second binomial
coefficients. The natural-number subtraction and the lower bound `d ≥ 1` are
retained explicitly.
-/

/-- For every integer degree `d ≥ 1`, the second-binomial decrement is `d - 1`. -/
theorem chooseTwo_sub_chooseTwo_pred (d : ℕ) (hd : 1 ≤ d) :
    d.choose 2 - (d - 1).choose 2 = d - 1 := by
  have hd0 : d ≠ 0 := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  simp only [Nat.succ_sub_one]
  rw [Nat.choose_succ_succ, Nat.choose_one_right]
  simp

end MathlibPlus.Combinatorics
