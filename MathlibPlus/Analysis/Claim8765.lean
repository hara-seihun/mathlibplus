import Mathlib

namespace MathlibPlus.Analysis

/-- Proof-free source assertion for the backward-induction invariant ratio
interval. -/
def terminalWeyl_ratio_interval_claim8765 : Prop :=
  ∀ (N k : ℕ) (a q : ℕ → ℝ) (lambda : ℝ),
    k + 1 < N →
    a 0 = 0 →
    (∀ j, 1 ≤ j → j < N → 0 < a j) →
    a N = 0 →
    0 < lambda →
    (∀ j, k + 1 ≤ j → j < N →
      lambda ≥ a j + a (j + 1)) →
    q (N - 1) = a (N - 1) / lambda →
    (∀ j, k + 1 ≤ j → j + 1 < N →
      q j = a j / (lambda - a (j + 1) * q (j + 1))) →
    ∀ j, k + 1 ≤ j → j < N →
      0 < q j ∧
        q j ≤ a j / (lambda - a (j + 1)) ∧
          a j / (lambda - a (j + 1)) ≤ 1

end MathlibPlus.Analysis
