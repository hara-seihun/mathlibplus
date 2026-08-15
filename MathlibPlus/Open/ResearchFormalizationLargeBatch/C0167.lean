import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim2553_uniformLowerBoundAwayFromHeightZero : Prop := by
  exact ∀ (Y₀ : ℝ), 0 < Y₀ → Y₀ < 1 / 2 →
    ∀ᶠ r in (atTop : Filter ℝ),
      ∀ Y x : ℝ, Y₀ ≤ Y → Y < 1 / 2 → 2 ≤ x →
        min x (x * Real.tanh (Y * Real.log r) - 1 / 2) ≥ x / 4

end MathlibPlus.Open.ResearchFormalizationLargeBatch
