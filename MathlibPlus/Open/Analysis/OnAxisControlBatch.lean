import Mathlib

namespace MathlibPlus.Open.Analysis.OnAxisControlBatch

/-- Claim 10858: the on-axis polynomial has no root in the exact admissible
    off-axis rectangle `[1/2, 3/2] + i [3/2, 5/2]`. -/
def claim10858 : Prop :=
  ∀ z : ℂ,
    ((1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ (3 / 2 : ℝ) ∧
      (3 / 2 : ℝ) ≤ z.im ∧ z.im ≤ (5 / 2 : ℝ)) →
      z ^ 2 + 1 ≠ 0

end MathlibPlus.Open.Analysis.OnAxisControlBatch
