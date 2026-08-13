import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The proposed global epsilon monotonicity is refuted throughout the first chamber. -/
def claim11850 (S : ℝ → ℝ → ℝ) : Prop :=
  ¬(∀ X : ℝ, 0 < X → ∀ ε : ℝ, 0 ≤ ε → S ε X ≤ S 0 X) ∧
  (∀ X : ℝ, 2 ≤ X → X < 3 → ∀ ε : ℝ, 0 < ε → S ε X > S 0 X)

/-- The epsilon derivative is positive on the same chamber. -/
def claim11851 (S : ℝ → ℝ → ℝ) : Prop :=
  ∀ X : ℝ, 2 ≤ X → X < 3 → ∀ ε : ℝ, 0 ≤ ε →
    deriv (fun e : ℝ => S e X) ε =
      Real.log 2 * (2 : ℝ) ^ (-(1 + ε))

end MathlibPlus.Open.Analysis
