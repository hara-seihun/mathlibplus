import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim2415_exactSecondMoment : Prop := by
  exact let h : ℝ → ℝ :=
      fun x => x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
    (∫ x : ℝ, x ^ 2 * h x) = 3 / (2 * Real.pi ^ 2)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
