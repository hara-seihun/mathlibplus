import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.O0331

def shell (n : ℕ) : ℂ := (2 * Complex.I) ^ n + (-2 * Complex.I) ^ n

def poissonMean (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) * shell n

def claim14202 : Prop :=
  (∀ k : ℕ,
    shell (4 * k) = (2 ^ (4 * k + 1) : ℂ) ∧
      shell (4 * k + 2) = (-(2 ^ (4 * k + 3)) : ℂ) ∧
      shell (2 * k + 1) = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 ≤ x →
        poissonMean x = ((2 * Real.exp (-x) * Real.cos (2 * x) : ℝ) : ℂ) ∧
        poissonMean x - ((2 * Real.exp (-x) : ℝ) : ℂ) =
          ((2 * Real.exp (-x) * (Real.cos (2 * x) - 1) : ℝ) : ℂ) ∧
        ‖poissonMean x - ((2 * Real.exp (-x) : ℝ) : ℂ)‖ ≤ C * Real.exp (-x))

end MathlibPlus.Open.Analysis.O0331
