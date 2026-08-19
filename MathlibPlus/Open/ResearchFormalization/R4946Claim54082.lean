import Mathlib
import MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R4946

open MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

private noncomputable def atomMeasure (weight location : ℝ) : Measure ℝ :=
  ENNReal.ofReal weight • Measure.dirac location

private noncomputable def explicitEpsilon : ℝ :=
  Real.rpow 2 (-100)

private noncomputable def explicitDyadicTail (k : ℕ) : ℝ :=
  Real.rpow 2 (-((k : ℝ) ^ 4))

private noncomputable def explicitB : ℝ :=
  4 - 2 * Real.exp targetTime * Real.cosh targetHeight

private noncomputable def explicitR : ℝ :=
  2 * explicitEpsilon * ∑' k : ℕ,
    if 4 ≤ k then
      (-1 : ℝ) ^ k * explicitDyadicTail k *
        Real.exp (targetTime * (k : ℝ) ^ 2) *
        Real.cosh ((k : ℝ) * targetHeight)
    else 0

private noncomputable def explicitW : ℝ :=
  (explicitB + explicitR) /
    (2 * Real.exp (9 * targetTime) * Real.cosh (3 * targetHeight))

private noncomputable def explicitSource : Measure ℝ :=
  atomMeasure 4 0 + atomMeasure 1 1 + atomMeasure 1 (-1) +
    atomMeasure explicitW 3 + atomMeasure explicitW (-3) +
    Measure.sum (fun k : ℕ =>
      if 4 ≤ k then
        atomMeasure (explicitEpsilon * explicitDyadicTail k) (k : ℝ) +
          atomMeasure (explicitEpsilon * explicitDyadicTail k) (-(k : ℝ))
      else 0)

/-- R-4946 claim 54082: the displayed positive even source has a target-ray
zero, with the exact epsilon, alternating tail, and weight normalization. -/
def claim54082_explicitPositiveEvenSource : Prop :=
  explicitW > 0 ∧
    PositiveEvenDiscreteSuperexponential explicitSource ∧
    heatTransform explicitSource targetTime targetPoint = 0

end MathlibPlus.Open.ResearchFormalization.R4946
