import Mathlib

namespace MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The interval-supported complex Fourier--Laplace transform. -/
noncomputable def endpointBandTransform
    (r : ℝ) (μ : ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  (μ.restrict (Set.Icc (-r) 0)).integral
    (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * z))
    (ContinuousLinearMap.mul ℝ ℂ)

/-- The weighted total-variation integral on the endpoint band. -/
noncomputable def endpointBandWeightedVariation
    (r : ℝ) (μ : ComplexMeasure ℝ) (y : ℝ) : ℝ :=
  ∫ τ : ℝ in Set.Icc (-r) 0, Real.exp (-y * τ) ∂μ.variation

/-- Claim 15435: a finite complex measure supported on the endpoint band
produces the displayed exponential transform and weighted variation. -/
def claim15435_endpointBandExponentialTransform : Prop :=
  ∀ (r : ℝ) (μ : ComplexMeasure ℝ),
    0 ≤ r →
      IsFiniteMeasure μ.variation →
        μ.variation.support ⊆ Set.Icc (-r) 0 →
          ∃ (B : ℂ → ℂ) (M : ℝ → ℝ),
            (∀ z : ℂ, B z = endpointBandTransform r μ z) ∧
              (∀ y : ℝ, M y = endpointBandWeightedVariation r μ y)

end

end MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435
