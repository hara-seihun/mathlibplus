import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6895_taylorRemainderForInversePowers : Prop := by
  exact ∀ (m : ℕ) (q : ℝ), |q| < 1 →
    |(1 - q) ^ (-(m : ℤ)) - 1 - (m : ℝ) * q| ≤
      ((m : ℝ) * (m + 1) / 2) * |q| ^ 2 /
        (1 - |q|) ^ (m + 2)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
