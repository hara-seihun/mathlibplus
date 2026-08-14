import Mathlib

namespace MathlibPlus.Open.Analysis.BatchShellSaddle

/-- The shell-pair phase and its unique real saddle point. -/
def shellPairSaddlePoint : Prop :=
  ∀ (n m : ℕ) (y : ℝ),
    0 < n →
    0 < m →
    let E : ℝ := Real.exp (2 * y)
    let aₙ : ℝ := Real.pi * (n : ℝ) ^ 2
    let aₘ : ℝ := Real.pi * (m : ℝ) ^ 2
    let phase : ℝ → ℝ :=
      fun d => aₙ * E * Real.exp (2 * d) + aₘ * E * Real.exp (-2 * d)
    let d₀ : ℝ := (1 / 2 : ℝ) * Real.log ((m : ℝ) / n)
    phase d₀ = 2 * Real.pi * n * m * E ∧
      (∀ d : ℝ, phase d₀ ≤ phase d) ∧
      (∀ d : ℝ, phase d = phase d₀ ↔ d = d₀)

end MathlibPlus.Open.Analysis.BatchShellSaddle
