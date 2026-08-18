import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0002Claim30

/-- Alternating reversal with positive extremal coefficients identifies the
polynomial value at one with both the coefficient sum and the coefficientwise
absolute-value sum. -/
def alternatingExtremalL1_claim30 : Prop :=
  ∀ (n : ℕ) (p q : ℕ → ℝ),
    (∀ k ≤ n, p k = (-1 : ℝ) ^ k * q (n - k)) →
    (∀ k ≤ n, 0 < p k) →
    (Polynomial.eval 1
        (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (p k) * Polynomial.X ^ k) =
      ∑ k ∈ Finset.range (n + 1), p k) ∧
    (∑ k ∈ Finset.range (n + 1), p k =
      ∑ r ∈ Finset.range (n + 1), |q r|)

end MathlibPlus.Open.ResearchFormalization.C0002Claim30
