import Mathlib

namespace MathlibPlus.Open.NumberTheory.PrimeSieveCensus

/-- Claim 947: in the prime-interval domain, an order-`m` interval with
coefficient `A` is contained in the order-`n` interval with coefficient `B`
under the displayed endpoint comparison, and prime existence transfers. -/
def primeIntervalContainment_claim947 : Prop :=
  ∀ (A B : ℝ) (m n : ℕ) (x : ℝ),
    2 ≤ x →
      A / (Real.log x) ^ m ≤ B / (Real.log x) ^ n →
        (∀ p : ℕ, x < (p : ℝ) →
          (p : ℝ) ≤ x * (1 + A / (Real.log x) ^ m) →
          (p : ℝ) ≤ x * (1 + B / (Real.log x) ^ n)) ∧
        ((∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
            (p : ℝ) ≤ x * (1 + A / (Real.log x) ^ m)) →
          ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
            (p : ℝ) ≤ x * (1 + B / (Real.log x) ^ n))

end MathlibPlus.Open.NumberTheory.PrimeSieveCensus
