import Mathlib

open scoped BigOperators
open MeasureTheory
open Set

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.CutoffKernel

/-- The exact endpoint-flat polynomial source. -/
def endpointFlatPolynomial (v : ℝ) : ℝ :=
  (1 - v ^ 2) * (v ^ 2 - (1 : ℝ) / 5)

/-- The disappearing summand at the internal cutoff. -/
def disappearingSummand (x : ℝ) : ℝ :=
  if x < Real.log ((3 : ℝ) / 2) then
    Real.exp (x / 2) / Real.sqrt 3 *
      endpointFlatPolynomial (2 * Real.exp x / 3)
  else 0

/-- The exact cutoff arithmetic kernel at c=3. -/
def cutoffArithmeticKernel (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt 3 *
      endpointFlatPolynomial (Real.exp x / 3) +
    disappearingSummand x

def cutoffPoint : ℝ := Real.log ((3 : ℝ) / 2)

/-- The exact kernel formula, continuity, one-sided summand derivatives, and
nonzero derivative jump in the admitted cutoff claim. -/
def cutoffArithmeticKernelHasExactJump : Prop :=
  (∀ x : ℝ, 0 < x → x < Real.log 3 →
    cutoffArithmeticKernel x =
      Real.exp (x / 2) / Real.sqrt 3 *
        (endpointFlatPolynomial (Real.exp x / 3) +
          if x < Real.log ((3 : ℝ) / 2) then
            endpointFlatPolynomial (2 * Real.exp x / 3)
          else 0)) ∧
  endpointFlatPolynomial (2 * Real.exp cutoffPoint / 3) = 0 ∧
  disappearingSummand cutoffPoint = 0 ∧
  ContinuousAt cutoffArithmeticKernel cutoffPoint ∧
  HasDerivAtFilter disappearingSummand
    (-8 / (5 * Real.sqrt 2))
      (nhdsWithin cutoffPoint (Iio cutoffPoint) ×ˢ pure cutoffPoint) ∧
  HasDerivAtFilter disappearingSummand 0
      (nhdsWithin cutoffPoint (Ioi cutoffPoint) ×ˢ pure cutoffPoint) ∧
  (∃ dLeft dRight : ℝ,
    HasDerivAtFilter cutoffArithmeticKernel dLeft
      (nhdsWithin cutoffPoint (Iio cutoffPoint) ×ˢ pure cutoffPoint) ∧
    HasDerivAtFilter cutoffArithmeticKernel dRight
      (nhdsWithin cutoffPoint (Ioi cutoffPoint) ×ˢ pure cutoffPoint) ∧
    dRight - dLeft = 8 / (5 * Real.sqrt 2)) ∧
  8 / (5 * Real.sqrt 2) ≠ 0


