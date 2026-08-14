import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Sharp uniform upper bound for the quadratic expression on the stated region. -/
def claim59747_quadraticSharpness : Prop :=
  (∀ t y : ℝ,
      t ≤ (1579 : ℝ) / 10000 →
      |y| ≤ (1 : ℝ) / 10 →
      (t + y ^ 2 / 2 ≤ (1629 : ℝ) / 10000 ∧
        (t + y ^ 2 / 2 = (1629 : ℝ) / 10000 ↔
          t = (1579 : ℝ) / 10000 ∧ |y| = (1 : ℝ) / 10))) ∧
    (∀ C : ℝ,
      (∀ t y : ℝ,
        t ≤ (1579 : ℝ) / 10000 →
        |y| ≤ (1 : ℝ) / 10 →
        t + y ^ 2 / 2 ≤ C) →
      (1629 : ℝ) / 10000 ≤ C)

end MathlibPlus.Open.Analysis
