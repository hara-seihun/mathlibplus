import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.CompactSupportChargeCancellation15414

noncomputable section

/-- The Fourier--Laplace channel carrier in Claim 15414. -/
noncomputable def channelTransform
    (κ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ t : ℝ,
    Complex.exp (Complex.I * z * (t : ℂ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; κ]

/-- The first moment of the Fourier--Laplace channel carrier. -/
noncomputable def channelFirstMoment
    (κ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ t : ℝ,
    (t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; κ]

/-- The normalized channel charge `L⁻¹ (∫ t exp(izt) dκ)/(∫ exp(izt) dκ)`. -/
noncomputable def channelCharge
    (κ : MeasureTheory.ComplexMeasure ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  ((1 / L : ℝ) : ℂ) *
    (channelFirstMoment κ z / channelTransform κ z)

/-- The total-variation weighted mass used as the cancellation numerator. -/
noncomputable def weightedVariationMass
    (κ : MeasureTheory.ComplexMeasure ℝ) (y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-y * t) ∂κ.variation

/-- The cancellation condition number at a nonzero channel value. -/
noncomputable def cancellationConditionNumber
    (κ : MeasureTheory.ComplexMeasure ℝ) (x y : ℝ) : ℝ :=
  weightedVariationMass κ y /
    ‖channelTransform κ ((x : ℂ) + (y : ℂ) * Complex.I)‖

/-- Compact support in the exact symmetric window `|t| ≤ T`. -/
def supportedInWindow
    (κ : MeasureTheory.ComplexMeasure ℝ) (T : ℝ) : Prop :=
  κ.variation.support ⊆ Set.Icc (-T) T

/-- Claim 15414: a finite complex measure supported in `|t| ≤ T_L` has
charge bounded by the window width times its total-variation cancellation
condition number.  The second conjunct records the stated order-one-charge
consequence on an `o(L)` window. -/
def compactSupportChargeCancellation_claim15414 : Prop :=
  (∀ (κ : MeasureTheory.ComplexMeasure ℝ) (L T x y : ℝ),
    0 < T →
    0 < L →
    IsFiniteMeasure κ.variation →
    supportedInWindow κ T →
    channelTransform κ ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 →
    ‖channelCharge κ L ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (T / L) * cancellationConditionNumber κ x y) ∧
  (∀ (κ : ℕ → MeasureTheory.ComplexMeasure ℝ)
      (L T x y : ℕ → ℝ) (c : ℝ),
    0 < c →
    Filter.Tendsto L Filter.atTop Filter.atTop →
    Filter.Tendsto (fun n => T n / L n) Filter.atTop (𝓝 0) →
    (∀ n : ℕ,
      0 < T n ∧
      0 < L n ∧
      IsFiniteMeasure (κ n).variation ∧
      supportedInWindow (κ n) (T n) ∧
      channelTransform (κ n)
          ((x n : ℂ) + (y n : ℂ) * Complex.I) ≠ 0 ∧
      c ≤ ‖channelCharge (κ n) (L n)
          ((x n : ℂ) + (y n : ℂ) * Complex.I)‖) →
    ∀ n : ℕ,
      c * L n / T n ≤ cancellationConditionNumber (κ n) (x n) (y n))

end

end MathlibPlus.Open.ResearchFormalization.CompactSupportChargeCancellation15414
