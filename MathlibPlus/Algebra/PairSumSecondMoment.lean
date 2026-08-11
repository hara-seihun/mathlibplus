import Mathlib

namespace MathlibPlus.Algebra.PairSumSecondMoment

/-!
# Pair-sum second moments

Claim 25919 is expanded over `ℝ` for a quadruple `(μ₀, μ₁, μ₂, μ₃)` with
`N` equal to its total. The six terms are the six unordered pairs, so no
unstated indexing convention is needed.
-/

/-- The first and second moments of the six pair sums, and their centered
second moment, have the displayed exact values. -/
theorem pairSumSecondMoment (μ₀ μ₁ μ₂ μ₃ N : ℝ)
    (hN : N = μ₀ + μ₁ + μ₂ + μ₃) :
    ((μ₀ + μ₁) + (μ₀ + μ₂) + (μ₀ + μ₃) +
        (μ₁ + μ₂) + (μ₁ + μ₃) + (μ₂ + μ₃) = 3 * N) ∧
      ((μ₀ + μ₁) ^ 2 + (μ₀ + μ₂) ^ 2 + (μ₀ + μ₃) ^ 2 +
        (μ₁ + μ₂) ^ 2 + (μ₁ + μ₃) ^ 2 + (μ₂ + μ₃) ^ 2 =
          2 * (μ₀ ^ 2 + μ₁ ^ 2 + μ₂ ^ 2 + μ₃ ^ 2) + N ^ 2) ∧
      (((μ₀ + μ₁) * (μ₀ + μ₁ - N) +
          (μ₀ + μ₂) * (μ₀ + μ₂ - N) +
          (μ₀ + μ₃) * (μ₀ + μ₃ - N) +
          (μ₁ + μ₂) * (μ₁ + μ₂ - N) +
          (μ₁ + μ₃) * (μ₁ + μ₃ - N) +
          (μ₂ + μ₃) * (μ₂ + μ₃ - N)) =
        2 * (μ₀ ^ 2 + μ₁ ^ 2 + μ₂ ^ 2 + μ₃ ^ 2 - N ^ 2)) := by
  subst N
  constructor
  · ring
  constructor
  · ring
  · ring

end MathlibPlus.Algebra.PairSumSecondMoment
