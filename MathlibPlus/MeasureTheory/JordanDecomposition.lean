import Mathlib

/-!
# Jordan sign masses

The real positive/negative-part identities from admitted claim `3873`.  The source
uses an unspecified interval and measure; those are explicit parameters here, and
its `L¹` norm is represented by the real set integral of `|r|`.
-/

open MeasureTheory

namespace MathlibPlus.MeasureTheory.JordanDecomposition

noncomputable section

/-- The mass of the positive part of a real source on a measurable restriction. -/
def positiveMass {α : Type*} [MeasurableSpace α]
    (r : α → ℝ) (I : Set α) (μ : Measure α) : ℝ :=
  ∫ x in I, (r x)⁺ ∂μ

/-- The mass of the negative part of a real source on a measurable restriction. -/
def negativeMass {α : Type*} [MeasurableSpace α]
    (r : α → ℝ) (I : Set α) (μ : Measure α) : ℝ :=
  ∫ x in I, (r x)⁻ ∂μ

/-- The real `L¹` mass of a source on a measurable restriction. -/
def l1Mass {α : Type*} [MeasurableSpace α]
    (r : α → ℝ) (I : Set α) (μ : Measure α) : ℝ :=
  ∫ x in I, |r x| ∂μ

/-- The signed integral of a source on a measurable restriction. -/
def signedMass {α : Type*} [MeasurableSpace α]
    (r : α → ℝ) (I : Set α) (μ : Measure α) : ℝ :=
  ∫ x in I, r x ∂μ

/-- Positive and negative Jordan masses recover both the `L¹` mass and the signed mass. -/
theorem jordanMassIdentities {α : Type*} [MeasurableSpace α]
    (r : α → ℝ) (I : Set α) (μ : Measure α) (hr : IntegrableOn r I μ) :
    positiveMass r I μ + negativeMass r I μ = l1Mass r I μ ∧
      positiveMass r I μ - negativeMass r I μ = signedMass r I μ := by
  have hI : Integrable r (μ.restrict I) := hr
  have hsign :=
    integral_eq_integral_pos_part_sub_integral_neg_part (μ := μ.restrict I) hI
  have habs :=
    integral_abs_eq_two_mul_integral_posPart_sub_integral (μ := μ.restrict I) hI
  have hsign' :
      (∫ x in I, r x ∂μ) =
        (∫ x in I, (r x)⁺ ∂μ) - (∫ x in I, (r x)⁻ ∂μ) := by
    simpa [PosPart.posPart, NegPart.negPart, Real.coe_toNNReal'] using hsign
  dsimp [positiveMass, negativeMass, l1Mass, signedMass]
  constructor <;> linarith [hsign', habs]

end

end MathlibPlus.MeasureTheory.JordanDecomposition
