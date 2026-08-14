import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- Claim 16751: one exceptional unimodal factor preserves unimodality. -/
def claim16751 : Prop :=
  ∀ (a b : ℕ → ℝ),
    (∃ N : ℕ, ∀ n, N < n → a n = 0) →
    (∃ N : ℕ, ∀ n, N < n → b n = 0) →
    (∀ n, 0 ≤ a n) →
    (∀ n, 0 ≤ b n) →
    (∀ n, 0 < n → a n ^ 2 ≥ a (n - 1) * a (n + 1)) →
    (∀ i j k, i ≤ j → j ≤ k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0) →
    (∃ m : ℕ,
      (∀ i j, i ≤ j → j ≤ m → b i ≤ b j) ∧
        (∀ i j, m ≤ i → i ≤ j → b j ≤ b i)) →
      ∃ m : ℕ,
        (∀ i j, i ≤ j → j ≤ m →
          (∑ k ∈ Finset.range (i + 1), a k * b (i - k)) ≤
            (∑ k ∈ Finset.range (j + 1), a k * b (j - k))) ∧
          (∀ i j, m ≤ i → i ≤ j →
            (∑ k ∈ Finset.range (j + 1), a k * b (j - k)) ≤
              (∑ k ∈ Finset.range (i + 1), a k * b (i - k)))

end MathlibPlus.Open.ResearchFormalization
