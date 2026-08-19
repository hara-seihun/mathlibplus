import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3423MinimalDivisor

noncomputable section

/-- Claim 50206: the fixed contextual binomial-gcd height has the exact
minimal-divisor characterization at the contextual Q(n). -/
def contextualMinimalDivisor_claim50206 : Prop :=
  let H : ℕ → ℕ → ℕ := fun n k =>
    n / Nat.gcd n (Nat.choose n k)
  let Q : ℕ → ℕ := fun n =>
    (Nat.factorization n).support.sup
      (fun p => p ^ Nat.factorization n p)
  let M : ℕ → ℕ → ℕ → Prop := fun n q d =>
    d ∣ n ∧ q < d ∧
      (∀ e : ℕ, e ∣ d → e < d → e ≤ q)
  ∀ n : ℕ,
    (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) →
      ∀ k : ℕ, 2 ≤ k → 2 * k ≤ n →
        0 < H n k ∧ H n k ∣ n ∧
          (H n k > Q n ↔
            ∃ d : ℕ, d ∣ H n k ∧ M n (Q n) d)

end

end MathlibPlus.Open.ResearchFormalization.R3423MinimalDivisor
