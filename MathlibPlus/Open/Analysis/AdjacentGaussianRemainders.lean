import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The stated bound for the difference of two adjacent Gaussian remainders. -/
def adjacentGaussianRemainderDifferenceBound : Prop :=
  ∀ (m : ℕ) (s B qInf u v : ℝ),
    0 ≤ B →
    qInf ≠ 0 →
    |(qInf - u) / qInf| ≤
      B * Real.exp (s - Real.pi * (m : ℝ) ^ 2) →
    |(qInf - v) / qInf| ≤
      B * Real.exp (s - Real.pi * ((m : ℝ) + 1) ^ 2) →
    |(v - u) / qInf| ≤
      B * (1 + Real.exp (-Real.pi)) *
        Real.exp (s - Real.pi * (m : ℝ) ^ 2)

end MathlibPlus.Open.Analysis
