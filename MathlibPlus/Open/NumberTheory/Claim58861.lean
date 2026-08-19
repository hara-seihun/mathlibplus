import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim58861

/-- Claim 58861: the retained prime-chain hypotheses force the next prime
condition and the divisibility reduction by three. -/
def primeChainDivisibilityClaim : Prop :=
  ∀ n u : ℕ,
    24 < n →
    (∀ k : ℕ, 1 ≤ k → k < n →
      (Nat.divisors (n - k)).card ≤ k + 2) →
    n = 840 * u →
    Nat.Prime (140 * u - 1) →
    Nat.Prime (210 * u - 1) →
    Nat.Prime (420 * u - 1) →
    Nat.Prime (840 * u - 1) →
    (Even u → Nat.Prime (105 * u - 1)) →
    (Odd u → Nat.Prime ((105 * u - 1) / 2)) →
    n - 3 = 3 * (280 * u - 1) ∧
      Nat.Prime (280 * u - 1) ∧
      (u % 3 = 1 → 3 ∣ (280 * u - 1)) ∧
      (u % 3 = 2 → 3 ∣ (140 * u - 1)) ∧
      (u % 3 = 1 → 3 < 280 * u - 1) ∧
      (u % 3 = 2 → 3 < 140 * u - 1) ∧
      3 ∣ u ∧
      ∃ N : ℕ, n = 2520 * N

end MathlibPlus.Open.NumberTheory.Claim58861
