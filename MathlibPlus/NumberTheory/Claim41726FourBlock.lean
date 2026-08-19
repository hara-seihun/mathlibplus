import Mathlib

namespace MathlibPlus.NumberTheory.Claim41726

/-- The exact totient and congruence criterion for the four-block terminal. -/
def arithmeticFourBlockCondition_claim41726 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    Nat.totient (3 * p) = 2 * (p - 1) ∧
      (p % 3 = 2 ↔ Nat.gcd (3 * p) (Nat.totient (3 * p)) = 1)

end MathlibPlus.NumberTheory.Claim41726
