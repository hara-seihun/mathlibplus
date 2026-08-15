import MathlibPlus.Open.Analysis.StieltjesContext

namespace MathlibPlus.Open.Analysis

def zhangWilliamsCoefficientEstimate : Prop :=
  stieltjesContext ∧
    ∀ n : ℕ, 1 ≤ n →
      |stieltjesConstants n| / (Nat.factorial (n - 1) : ℝ) ≤
        4 * Real.sqrt 2 * (2 / (Real.pi * Real.exp 1)) ^ n

end MathlibPlus.Open.Analysis
