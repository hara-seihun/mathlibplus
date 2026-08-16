import Mathlib

namespace MathlibPlus.Open.Analysis.EndpointReserveMovingFourierAnnulusClaim15450

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The Fourier-series density in the canonical negative shifted tail. -/
noncomputable def canonicalNegativeTailDensity
    (L : ℝ) (qhat : ℝ → ℂ) (τ : ℝ) : ℂ :=
  if τ ≤ 0 then
    (-1 / 2 : ℂ) *
        Complex.exp (((L - τ) / 2 : ℝ) : ℂ) *
      ∑' k : ℕ,
        if 0 < k then qhat ((k : ℝ) * Real.exp (L - τ)) else 0
  else 0

/-- The exact density relation for the canonical negative shifted-tail measure. -/
def canonicalNegativeTail
    (L : ℝ) (qhat : ℝ → ℂ) (μminus : ComplexMeasure ℝ) : Prop :=
  ∀ (f : ℝ → ℂ),
    Continuous f →
      HasCompactSupport f →
        μminus.integral f (ContinuousLinearMap.mul ℝ ℂ) =
          ∫ τ : ℝ, f τ * canonicalNegativeTailDensity L qhat τ ∂volume

/-- The negative endpoint-band weighted total variation. -/
noncomputable def negativeEndpointReserve
    (r y : ℝ) (μminus : ComplexMeasure ℝ) : ℝ :=
  ∫ τ : ℝ in Set.Icc (-r) 0, Real.exp (-y * τ) ∂μminus.variation

/-- Claim 15450: restriction of the canonical negative tail to the endpoint
band `[-r,0]` is the displayed moving Fourier-annulus integral. -/
def claim15450_endpointReserveMovingFourierAnnulus : Prop :=
  ∀ (L r y : ℝ) (qhat : ℝ → ℂ) (μminus : ComplexMeasure ℝ),
    0 ≤ r →
      canonicalNegativeTail L qhat μminus →
        negativeEndpointReserve r y μminus =
          (1 / 2) * Real.exp (-y * L) *
            ∫ u in Real.exp L..Real.exp (L + r),
              Real.rpow u (y - 1 / 2) *
                ‖∑' k : ℕ,
                  if 0 < k then qhat ((k : ℝ) * u) else 0‖

end

end MathlibPlus.Open.Analysis.EndpointReserveMovingFourierAnnulusClaim15450
