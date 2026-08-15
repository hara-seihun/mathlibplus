import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open

/-- Finite-prefix freedom of the two next-rank quantities. -/
def formalizationClaim59737 : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∀ a : ℕ → ℚ, ∀ b : ℕ → ℕ,
      ∃ m : ℕ → ℚ, ∃ μ : ℕ → ℕ,
        (∀ r ≤ N, m r = a r) ∧
        (∀ r ≤ N, μ r = b r) ∧
        m (N + 1) ≠ (2 : ℚ) * (N.factorial : ℚ) * m N ∧
        μ (N + 1) ≠ (N - 1).factorial

end MathlibPlus.Open
