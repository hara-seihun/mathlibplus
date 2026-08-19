import MathlibPlus.Open.Analysis.Claim3381

namespace MathlibPlus.Open.Analysis.Claim3382

open MathlibPlus.Open.Analysis.Claim3381

/-- Uniform square-root-window curvature asymptotic for the consecutive
mixed-shift determinant tower. -/
def mesoscopicCurvatureAsymptotic : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n →
          ∀ m : ℕ, 1 ≤ m →
            (m : ℝ) ≤ A * Real.sqrt (n : ℝ) →
              |L m n - 2 * gamma n * (m : ℝ) / (n : ℝ)| ≤
                C *
                  ((m : ℝ) / ((n : ℝ) * w n ^ 2) +
                    (m : ℝ) ^ 2 / (n : ℝ) ^ 2)

end MathlibPlus.Open.Analysis.Claim3382
