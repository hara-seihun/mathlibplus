import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim4226

noncomputable def poissonWeight4226 (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

def consecutivePoissonWeightRecurrences_claim4226 : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ n : ℕ,
      poissonWeight4226 x (n + 1) =
        x * poissonWeight4226 x n / ((n : ℝ) + 1)) ∧
    poissonWeight4226 x 1 = x * poissonWeight4226 x 0 ∧
    (∀ n : ℕ, 0 < n →
      (n : ℝ) * poissonWeight4226 x n ^ 2 =
        ((n : ℝ) + 1) * poissonWeight4226 x (n - 1) *
          poissonWeight4226 x (n + 1)) ∧
    (∀ n : ℕ, 0 < n →
      poissonWeight4226 x n =
        Real.sqrt (((n : ℝ) + 1) / (n : ℝ)) *
          Real.sqrt
            (poissonWeight4226 x (n - 1) *
              poissonWeight4226 x (n + 1)))

end MathlibPlus.Open.Analysis.Claim4226

end
