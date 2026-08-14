import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.R0118

private def pointKernel (n : ℕ) (r x : ℝ) : ℝ :=
  x * (x - n) * Real.exp (-Real.pi * r * x ^ 2)

private def pointMinor (n : ℕ) (r₁ r₂ x₁ x₂ : ℝ) : ℝ :=
  pointKernel n r₁ x₁ * pointKernel n r₂ x₂ -
    pointKernel n r₁ x₂ * pointKernel n r₂ x₁

/-- The point kernel itself is not totally positive, so integrated positivity
cannot be inferred pointwise. -/
def claim_18075 : Prop :=
  ¬ (∀ (n : ℕ) (r₁ r₂ x₁ x₂ : ℝ),
      0 < r₁ → r₁ < r₂ →
      (n : ℝ) ≤ x₁ → x₁ < n + 1 →
      (n : ℝ) ≤ x₂ → x₂ < n + 1 → x₁ < x₂ →
      0 < pointMinor n r₁ r₂ x₁ x₂)

end MathlibPlus.Open.R0118
