import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 59938: Gaussian-ratio propagation from an initial bound. -/
def gaussian_ratio_propagation
    (d : ℕ → ℝ) (B s : ℝ) (m0 : ℕ) : Prop :=
  (|d m0| ≤ B * Real.exp (s - Real.pi * (m0 : ℝ) ^ 2) ∧
      (∀ k : ℕ, m0 ≤ k →
        |d (k + 1)| ≤
          Real.exp (-Real.pi * (2 * (k : ℝ) + 1)) * |d k|)) →
    ∀ m : ℕ, m0 ≤ m →
      |d m| ≤ B * Real.exp (s - Real.pi * (m : ℝ) ^ 2)

end MathlibPlus.Open.Analysis
