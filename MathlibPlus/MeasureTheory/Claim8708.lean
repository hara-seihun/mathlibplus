import Mathlib

/-!
# Ordered pairs touching an off-window set

Claim 8708 records the inclusion-exclusion mass of ordered pairs for which at
least one coordinate lies in an off-window set.  The source does not spell out
its probability-space interface; the product-measure theorem below makes the
natural probability-measure and measurable-set conventions explicit, while the
last two theorems retain the scalar identity and bound.
-/

open MeasureTheory Set

namespace MathlibPlus.MeasureTheory.Claim8708

noncomputable section

/-- Product-measure realization of the ordered-pair mass in admitted claim 8708. -/
theorem measure_offWindowPairMass
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {O : Set α} (hO : MeasurableSet O) :
    (ν.prod ν) (O ×ˢ univ ∪ univ ×ˢ O) = 1 - (1 - ν O) ^ 2 := by
  have hOprod : MeasurableSet (O ×ˢ (univ : Set α)) := hO.prod MeasurableSet.univ
  have hunivO : MeasurableSet ((univ : Set α) ×ˢ O) := MeasurableSet.univ.prod hO
  have hU : MeasurableSet (O ×ˢ univ ∪ (univ : Set α) ×ˢ O) := hOprod.union hunivO
  have hcomp : (O ×ˢ (univ : Set α) ∪ (univ : Set α) ×ˢ O)ᶜ = Oᶜ ×ˢ Oᶜ := by
    ext x
    simp
  have hcomp_measure :=
    measure_compl (μ := ν.prod ν) hU.compl (measure_ne_top (ν.prod ν) _)
  rw [compl_compl] at hcomp_measure
  rw [hcomp] at hcomp_measure
  simpa only [Measure.prod_prod (Oᶜ) (Oᶜ), measure_univ,
    measure_compl (μ := ν) hO (measure_ne_top ν O), pow_two] using hcomp_measure

/-- Scalar inclusion-exclusion identity from admitted claim 8708. -/
theorem offWindowPairMass_eq (q : ℝ) :
    1 - (1 - q) ^ 2 = 2 * q - q ^ 2 := by
  ring

/-- The ordered-pair mass is at most twice the one-coordinate mass. -/
theorem offWindowPairMass_le_two_mul (q : ℝ) :
    1 - (1 - q) ^ 2 ≤ 2 * q := by
  nlinarith [sq_nonneg q]

end

end MathlibPlus.MeasureTheory.Claim8708
