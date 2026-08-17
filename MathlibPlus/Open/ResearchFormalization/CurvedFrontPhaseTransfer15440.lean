import Mathlib
import MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435

open MeasureTheory
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.CurvedFrontPhaseTransfer15440

noncomputable section

noncomputable def curvedArcLoad
    (X Pi : ℂ → ℂ) (γ : ℝ → ℂ) (S : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..S,
    (‖deriv X (γ t) / X (γ t)‖ +
      ‖deriv Pi (γ t) / Pi (γ t)‖) * ‖deriv γ t‖

def continuousPhaseLiftOnArc
    (B : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ) (S : ℝ) : Prop :=
  ContinuousOn θ (Set.Icc 0 S) ∧
    ∀ t : ℝ, t ∈ Set.Icc 0 S →
      Complex.exp (Complex.I * (θ t : ℂ)) =
        B (γ t) / (‖B (γ t)‖ : ℂ)

/-- Claim 15440: transfer of the increasing phase on a curved Stokes front
from the projective field to the endpoint-band transform.  The leadership
bound is pointwise on the whole arc, so it controls the continuous phase lift
rather than only its endpoint values. -/
def curvedFrontPhaseTransfer_claim15440 : Prop :=
  ∀ (r : ℝ) (μ : ComplexMeasure ℝ)
    (L S ε : ℝ) (U : Set ℂ)
    (γ : ℝ → ℂ) (y : ℝ → ℝ)
    (X Pi E : ℂ → ℂ) (θ : ℝ → ℝ),
    0 ≤ r →
      IsFiniteMeasure μ.variation →
      μ.variation.support ⊆ Set.Icc (-r) 0 →
      0 < L →
      0 < S →
      0 ≤ ε →
      ε < 1 →
      IsOpen U →
      Set.range γ ⊆ U →
      AnalyticOnNhd ℂ (MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ) U →
      AnalyticOnNhd ℂ X U →
      AnalyticOnNhd ℂ Pi U →
      AnalyticOnNhd ℂ E U →
      (∀ t : ℝ, t ∈ Set.Icc 0 S →
        γ t = (t : ℂ) + Complex.I * (y t : ℂ)) →
      ContDiffOn ℝ 1 y (Set.Icc 0 S) →
      ContDiffOn ℝ 1 γ (Set.Icc 0 S) →
      (∀ t : ℝ, t ∈ Set.Icc 0 S →
        ‖Pi (γ t)‖ = 1 ∧
          X (γ t) ≠ 0 ∧
          Pi (γ t) ≠ 0 ∧
          MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ (γ t) ≠ 0 ∧
          (MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ (γ t) + E (γ t)) ≠ 0) →
      (∀ t : ℝ, t ∈ Set.Icc 0 S →
        Pi (γ t) =
          -Complex.exp (Complex.I * (L : ℂ) * γ t) * X (γ t) /
            (MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ (γ t) + E (γ t))) →
      (∀ t : ℝ, t ∈ Set.Icc 0 S →
        ‖E (γ t)‖ ≤ ε *
          ‖MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ (γ t)‖) →
      continuousPhaseLiftOnArc
        (MathlibPlus.Open.Analysis.EndpointBandExponentialTransformClaim15435.endpointBandTransform r μ)
        γ θ S →
      θ S - θ 0 ≥
        L * S - curvedArcLoad X Pi γ S - 2 * Real.arcsin ε

end

end MathlibPlus.Open.ResearchFormalization.CurvedFrontPhaseTransfer15440
