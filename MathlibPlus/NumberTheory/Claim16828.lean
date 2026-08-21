-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.NumberTheory.Claim16828

/-- Claim 16828: divisor counts multiply for positive coprime factors. -/
theorem card_divisors_mul_of_coprime
    {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) (hcop : m.Coprime n) :
    (m * n).divisors.card = m.divisors.card * n.divisors.card := by
  exact Nat.Coprime.card_divisors_mul hcop

/-- The coprimality premise cannot be dropped. -/
theorem card_divisors_mul_not_unconditional :
    ¬ (∀ m n : ℕ,
      (m * n).divisors.card = m.divisors.card * n.divisors.card) := by
  intro h
  have h22 := h 2 2
  have hbad : (2 * 2).divisors.card ≠
      (2 : ℕ).divisors.card * (2 : ℕ).divisors.card := by
    native_decide
  exact hbad h22

end MathlibPlus.NumberTheory.Claim16828
