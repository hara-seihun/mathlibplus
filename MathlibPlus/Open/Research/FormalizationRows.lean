import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

/-- The rising product appearing in the cleared-row formulas. -/
def clearedRising (x : ℝ) (r : ℕ) : ℝ :=
  ∏ i ∈ Finset.range r, (x + (i : ℝ))

/-- The cleared row polynomial, with the admitted initial normalization and recurrence. -/
def clearedQ : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, b => 2 * b
  | n + 2, m, b =>
      let N : ℕ := n + 2
      (2 * b + m + 2 * (N : ℝ)) * clearedQ (n + 1) (m + 1) b +
        (-1 : ℝ) ^ N * (m + 2 * (N : ℝ)) * clearedRising (m + 1) (n + 1) /
          (Nat.factorial N : ℝ)

/-- Admitted positive odd two-step row formula. -/
def claim1580 : Prop :=
  ∀ (d n : ℕ) (m b : ℝ),
    (1 ≤ d ∧ 1 ≤ n ∧ n ≤ d ∧ 3 ≤ n ∧ Odd n ∧
        m = ((d - n : ℕ) : ℝ)) →
      clearedQ n m b =
        (2 * b + m + 2 * (n : ℝ)) *
            (2 * b + m + 2 * (n : ℝ) - 1) *
            clearedQ (n - 2) (m + 2) b +
          clearedRising (m + 2) (n - 2) /
              (Nat.factorial n : ℝ) *
            (2 * (n : ℝ) * b * (m + 2 * (n : ℝ) - 1) +
              ((n - 1 : ℕ) : ℝ) * (m + 2 * (n : ℝ)) *
                (m + 2 * (n : ℝ) + 1))

end

end MathlibPlus.Open.Research
