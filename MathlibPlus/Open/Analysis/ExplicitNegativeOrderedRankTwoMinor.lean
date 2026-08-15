import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The explicit rank-two minor and ordered-cell counterexample from admitted claim 59532. -/
def explicitNegativeOrderedRankTwoMinor : Prop :=
  let K : ℝ → ℝ → ℝ := fun x u =>
    x * (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
      Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))
  let x₁ : ℝ := 1 / 2
  let x₂ : ℝ := 3 / 2
  let u₁ : ℝ := -Real.log 4
  let u₂ : ℝ := 0
  u₁ < u₂ ∧
    x₁ ∈ Set.Ico (0 : ℝ) 1 ∧
    x₂ ∈ Set.Ico (1 : ℝ) 2 ∧
    K x₁ u₁ * K x₂ u₂ - K x₁ u₂ * K x₂ u₁ < 0

end MathlibPlus.Open.Analysis
