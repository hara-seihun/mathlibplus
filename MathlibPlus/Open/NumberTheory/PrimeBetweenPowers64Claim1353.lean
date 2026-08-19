import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- Claim 1353: every consecutive pair of positive 64th powers contains a
prime strictly between its endpoints. -/
def primeBetweenConsecutiveSixtyFourthPowers : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ,
    Nat.Prime p ∧ n ^ 64 < p ∧ p < (n + 1) ^ 64

end MathlibPlus.Open.NumberTheory
