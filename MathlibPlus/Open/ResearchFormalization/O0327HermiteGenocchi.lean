import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0327HermiteGenocchi

open MeasureTheory
open Set
open scoped BigOperators

abbrev EndpointMeasure := MeasureTheory.ComplexMeasure ℝ

/-- The endpoint-band exponential transform on the stated interval. -/
noncomputable def endpointTransform (μ : EndpointMeasure) (r : ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ τ in Set.Icc (-r) 0,
    Complex.exp (Complex.I * (τ : ℂ) * z)
      ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]

/-- The weighted variation appearing at height `y`. -/
noncomputable def endpointWeightedVariation
    (μ : EndpointMeasure) (r y : ℝ) : ℝ :=
  ∫ τ in Set.Icc (-r) 0, Real.exp (-y * τ) ∂μ.variation

/-- A horizontal trace of the endpoint transform. -/
noncomputable def endpointTrace (μ : EndpointMeasure) (r y : ℝ) (x : ℝ) : ℂ :=
  endpointTransform μ r ((x : ℂ) + (y : ℂ) * Complex.I)

/-- The horizontal `n`th derivative of the endpoint transform. -/
noncomputable def endpointHorizontalDerivative
    (μ : EndpointMeasure) (r y : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv n (endpointTrace μ r y) x

/-- The real barycentric denominator at a node. -/
def endpointBarycentricDenominator {n : ℕ}
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  Finset.prod (Finset.univ.erase j) (fun k => x j - x k)

/-- The order-`n` barycentric divided difference of the horizontal trace. -/
noncomputable def endpointDividedDifference {n : ℕ}
    (μ : EndpointMeasure) (r y : ℝ) (x : Fin (n + 1) → ℝ) : ℂ :=
  ∑ j : Fin (n + 1),
    endpointTrace μ r y (x j) /
      (endpointBarycentricDenominator x j : ℂ)

/--
Hermite--Genocchi endpoint upper bound (Claim 15438).  The measure is finite
and supported on `[-r, 0]`; the horizontal derivative and the divided
 difference at distinct real nodes have the stated endpoint bounds.
-/
def claim15438 : Prop :=
  ∀ (μ : EndpointMeasure) (r y : ℝ) (n : ℕ)
    (x : Fin (n + 1) → ℝ),
    0 ≤ r →
    IsFiniteMeasure μ.variation →
    μ.variation (Set.Icc (-r) 0)ᶜ = 0 →
    (∀ u v : Fin (n + 1), u ≠ v → x u ≠ x v) →
    (∀ t : ℝ,
      ‖endpointHorizontalDerivative μ r y n t‖ ≤
        r ^ n * endpointWeightedVariation μ r y) ∧
      ‖endpointDividedDifference μ r y x‖ ≤
        r ^ n * endpointWeightedVariation μ r y / (Nat.factorial n : ℝ)

end MathlibPlus.Open.ResearchFormalization.O0327HermiteGenocchi
