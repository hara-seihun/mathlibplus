import Mathlib

namespace MathlibPlus.Open.Combinatorics

def oneSidedToeplitz (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i ≤ j then a (j - i) else 0

def pfTwoSequence (a : ℕ → ℝ) : Prop :=
  ∀ (i₁ i₂ j₁ j₂ : ℕ),
    i₁ < i₂ → j₁ < j₂ →
    0 ≤ oneSidedToeplitz a i₁ j₁ * oneSidedToeplitz a i₂ j₂ -
      oneSidedToeplitz a i₁ j₂ * oneSidedToeplitz a i₂ j₁

def noInternalZeros (a : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- For a nonnegative sequence with no internal zeros, PF₂ is log-concavity. -/
def pfTwoCharacterization : Prop :=
  ∀ (a : ℕ → ℝ),
    (∀ n, 0 ≤ a n) →
    noInternalZeros a →
    (pfTwoSequence a ↔ ∀ n, a (n + 1) ^ 2 ≥ a n * a (n + 2))

end MathlibPlus.Open.Combinatorics
