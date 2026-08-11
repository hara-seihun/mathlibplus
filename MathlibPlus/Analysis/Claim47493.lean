import Mathlib

namespace MathlibPlus.Analysis.Claim47493

/-- Algebraic form of the two-query affine-sign area formula: the initial
variance is `a²+b²`, and the two possible first-query residual variances are
`b²` and `a²`. -/
theorem twoSignAffineArea_claim47493
    (a b : ℝ) :
    a ^ 2 + b ^ 2 + min (a ^ 2) (b ^ 2) =
      min (a ^ 2 + b ^ 2 + b ^ 2) (a ^ 2 + b ^ 2 + a ^ 2) := by
  by_cases h : b ^ 2 ≤ a ^ 2
  · rw [min_eq_right h]
    have hsum : a ^ 2 + b ^ 2 + b ^ 2 ≤ a ^ 2 + b ^ 2 + a ^ 2 := by
      nlinarith
    rw [min_eq_left hsum]
  · have h' : a ^ 2 ≤ b ^ 2 := le_of_not_ge h
    rw [min_eq_left h']
    have hsum : a ^ 2 + b ^ 2 + a ^ 2 ≤ a ^ 2 + b ^ 2 + b ^ 2 := by
      nlinarith
    rw [min_eq_right hsum]

end MathlibPlus.Analysis.Claim47493
