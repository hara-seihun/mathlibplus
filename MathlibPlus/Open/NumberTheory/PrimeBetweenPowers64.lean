import MathlibPlus.Basic

namespace MathlibPlus.Open.NumberTheory

/-! Claim 1782: a prime lies strictly between every consecutive pair of
positive 64th powers. -/

/-- Every consecutive pair of positive 64th powers contains a prime strictly
between its endpoints. -/
def primeBetweenPowers64_claim1782 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ,
    Nat.Prime p ∧ n ^ 64 < p ∧ p < (n + 1) ^ 64

end MathlibPlus.Open.NumberTheory
