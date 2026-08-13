import Mathlib

namespace MathlibPlus.NumberTheory.DivisorGap

/-- The number of positive divisors, using Mathlib's `Nat.divisors` convention. -/
def positive_divisor_count (m : ℕ) : ℕ := (Nat.divisors m).card

/-- The shifted divisor-count condition `τ(n-k) ≤ k+2`. -/
def divisor_gap_condition (n k : ℕ) : Prop :=
  positive_divisor_count (n - k) ≤ k + 2

/-- A divisor-gap witness as defined in admitted claim 57048. -/
def divisor_gap_witness (n : ℕ) : Prop :=
  n > 24 ∧ ∀ k : ℕ, 1 ≤ k → k < n → divisor_gap_condition n k

end MathlibPlus.NumberTheory.DivisorGap
