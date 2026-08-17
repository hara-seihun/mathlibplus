import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.C0106Claim1651

noncomputable section

/-- The explicit second-strip amplitude from the closed `(n,2)` minor ratio. -/
def W1651 (n d : ℕ) : ℚ :=
  (((((d + 1 : ℕ) : ℚ) * ((d + n : ℕ) : ℚ) *
      ((d : ℚ) ^ 2 + (d : ℚ) - 2 * (n : ℚ) - 2) *
      ∏ r ∈ (Finset.Icc 2 (n - 1)), ((d : ℚ) - (r : ℚ)))) /
    (2 * (n : ℚ) * ((n + 1 : ℕ) : ℚ) *
      (Nat.factorial (n - 2) : ℚ)))

/-- The polynomial `P_n(m)` with its coefficient carrier exposed. -/
def PPolynomial1651 (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((n : ℚ) ^ 2 - 2 * (n : ℚ) - 1) * Polynomial.X ^ 2 +
    Polynomial.C
      (2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + 3) *
      Polynomial.X +
    Polynomial.C
      (((n : ℚ) - 1) ^ 2 * ((n - 2 : ℕ) : ℚ) * ((n + 1 : ℕ) : ℚ))

/-- The adjacent amplitude contribution in the odd two-step remainder, namely
`2 b W_(n-1)(d) + (d+n)W_(n-1)(d)-W_n(d)`. -/
def adjacentAmplitudeContribution1651 (n m : ℕ) : Polynomial ℚ :=
  Polynomial.C (2 * W1651 (n - 1) (m + n)) * Polynomial.X +
    Polynomial.C
      (((m + n + n : ℕ) : ℚ) * W1651 (n - 1) (m + n) -
        W1651 n (m + n))

/-- Claim 1651: the exact adjacent ratio, its cleared `P_n` identity, and
coefficientwise positivity of the resulting amplitude contribution. -/
def claim1651 : Prop :=
  ∀ (n m : ℕ), 5 ≤ n →
    let d : ℕ := m + n
    (W1651 n d / W1651 (n - 1) d =
      (((n - 1 : ℕ) : ℚ) * ((d + n : ℕ) : ℚ) *
        ((d - n + 1 : ℕ) : ℚ) *
        ((d : ℚ) ^ 2 + (d : ℚ) - 2 * (n : ℚ) - 2)) /
        (((n + 1 : ℕ) : ℚ) * ((n - 2 : ℕ) : ℚ) *
          ((d + n - 1 : ℕ) : ℚ) *
          ((d : ℚ) ^ 2 + (d : ℚ) - 2 * (n : ℚ)))) ∧
    (((d + n : ℕ) : ℚ) - W1651 n d / W1651 (n - 1) d =
      (((d + n : ℕ) : ℚ) * ((d + n + 1 : ℕ) : ℚ) *
        Polynomial.eval (m : ℚ) (PPolynomial1651 n)) /
        (((n - 2 : ℕ) : ℚ) * ((n + 1 : ℕ) : ℚ) *
          ((d + n - 1 : ℕ) : ℚ) *
          ((d : ℚ) ^ 2 + (d : ℚ) - 2 * (n : ℚ)))) ∧
    (0 < ((n : ℚ) ^ 2 - 2 * (n : ℚ) - 1) ∧
      0 < (2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + 3) ∧
      0 < (((n : ℚ) - 1) ^ 2 * ((n - 2 : ℕ) : ℚ) *
        ((n + 1 : ℕ) : ℚ))) ∧
    (0 < ((n + 1 : ℕ) : ℚ) ∧
      0 < ((n - 2 : ℕ) : ℚ) ∧
      0 < ((d + n - 1 : ℕ) : ℚ) ∧
      0 < ((d : ℚ) ^ 2 + (d : ℚ) - 2 * (n : ℚ))) ∧
    (0 < (PPolynomial1651 n).coeff 0 ∧
      0 < (PPolynomial1651 n).coeff 1 ∧
      0 < (PPolynomial1651 n).coeff 2 ∧
      ∀ k : ℕ, 3 ≤ k → (PPolynomial1651 n).coeff k = 0) ∧
    (∀ k : ℕ,
      0 ≤ (adjacentAmplitudeContribution1651 n m).coeff k)

end

end MathlibPlus.Open.Algebra.C0106Claim1651
