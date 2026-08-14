import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- The number of positive divisors of a positive natural number. -/
def positiveDivisorCount (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter (fun d => d ∣ m)).card

/-- The maximum of `m + τ(m)` over positive natural numbers `m < n`. -/
def divisorSumMaximum (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sup (fun m => m + positiveDivisorCount m)

/-- Exact formal statement of the admitted divisor-bound characterization. -/
def divisorBoundCharacterization : Prop :=
  ∀ n : ℕ, 24 < n →
    (divisorSumMaximum n ≤ n + 2 ↔
      ¬ ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ m + positiveDivisorCount m > n + 2)

end MathlibPlus.Open.NumberTheory
