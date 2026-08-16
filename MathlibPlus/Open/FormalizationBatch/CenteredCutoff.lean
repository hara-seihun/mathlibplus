import Mathlib

open scoped BigOperators
open MeasureTheory
open Set

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.CenteredCutoff

/-- The same exact endpoint-flat polynomial used by the centered claim. -/
def endpointFlatPolynomial (v : ℝ) : ℝ :=
  (1 - v ^ 2) * (v ^ 2 - (1 : ℝ) / 5)

/-- The exact c=3 cutoff kernel used before centering. -/
def cutoffArithmeticKernel (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt 3 *
    (endpointFlatPolynomial (Real.exp x / 3) +
      if x < Real.log ((3 : ℝ) / 2) then
        endpointFlatPolynomial (2 * Real.exp x / 3)
      else 0)

def centeringPoint : ℝ := Real.log 3 / 2

def centeredSwitchPoint : ℝ :=
  Real.log ((3 : ℝ) / 2) - centeringPoint

/-- The centered kernel from the admitted statement. -/
def centeredKernel (y : ℝ) : ℝ :=
  (cutoffArithmeticKernel (centeringPoint + y) +
      cutoffArithmeticKernel (centeringPoint - y)) / 2

/-- The reflected point is smooth, and centering halves the exact jump. -/
def centeredCutoffHasExactJump : Prop :=
  centeringPoint - centeredSwitchPoint = Real.log 2 ∧
  Real.log ((3 : ℝ) / 2) < Real.log 2 ∧
  DifferentiableAt ℝ cutoffArithmeticKernel (Real.log 2) ∧
  (∃ dLeft dRight : ℝ,
    HasDerivAtFilter centeredKernel dLeft
      (nhdsWithin centeredSwitchPoint (Iio centeredSwitchPoint) ×ˢ pure centeredSwitchPoint) ∧
    HasDerivAtFilter centeredKernel dRight
      (nhdsWithin centeredSwitchPoint (Ioi centeredSwitchPoint) ×ˢ pure centeredSwitchPoint) ∧
    dRight - dLeft = 4 / (5 * Real.sqrt 2)) ∧
  (4 / (5 * Real.sqrt 2)) ^ 2 = (8 : ℝ) / 25


