import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Probability.Claim48380_48381

noncomputable section

/-- Expectation on the source probability space. -/
def expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω ∂μ

/-- Variance in the source probability-space carrier. -/
def variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  expectation μ (fun ω => (f ω) ^ 2) - (expectation μ f) ^ 2

/-- Covariance in the source probability-space carrier. -/
def covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  expectation μ (fun ω => f ω * g ω) -
    expectation μ f * expectation μ g

def booleanValued {Ω : Type*} (f : Ω → ℝ) : Prop :=
  ∀ ω : Ω, f ω = 1 ∨ f ω = -1

/-- Claim 48380: Boolean random variables on an arbitrary probability space
satisfy the covariance bound by the smaller variance. -/
def claim48380_covarianceBound : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ),
    Measurable X → Measurable Y →
      booleanValued X → booleanValued Y →
        covariance μ X Y ≤ min (variance μ X) (variance μ Y)

/-- Claim 48381: Boolean random variables satisfy the absolute variance
差 bound by the variance of their difference. -/
def claim48381_varianceDifferenceBound : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ),
    Measurable X → Measurable Y →
      booleanValued X → booleanValued Y →
        |variance μ X - variance μ Y| ≤
          variance μ (fun ω => X ω - Y ω)

end

end MathlibPlus.Open.Probability.Claim48380_48381
