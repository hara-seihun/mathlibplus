import Mathlib

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 14281: one-separated active negative-shift data. -/
def oneSeparatedActiveNegativeShiftData_14281 : Prop := by
  classical
  exact ∃ (h a : ℕ → ℝ) (μ : MeasureTheory.SignedMeasure ℝ),
    (∀ j, h j < h (j + 1)) ∧
    Tendsto h atTop atTop ∧
    (∀ j, 1 ≤ h (j + 1) - h j) ∧
    (∀ j, a j ≠ 0) ∧
    Summable (fun j => |a j|) ∧
    μ.variation Set.univ ≠ ⊤ ∧
    (∀ s, MeasurableSet s →
      μ s = ∑' j, if -h j ∈ s then a j else 0)

end

end MathlibPlus.Open.Analysis
