import Mathlib
import MathlibPlus.Open.Analysis.CHJWeightedCoarea

open MeasureTheory

namespace MathlibPlus.Open.Analysis.CHJIntervalStep

noncomputable section

/-- The mass of the unnormalised interval step. -/
def intervalStepMass (a b : ℝ) : ℝ :=
  ∫ _u in a..b, (1 : ℝ)

/-- The reciprocal endpoint and weighted-bulk cost of an interval step. -/
def intervalStepCostNumerator (a b : ℝ) : ℝ :=
  a⁻¹ + b⁻¹ + ∫ u in a..b, u⁻¹

/-- The first-moment numerator of an interval step. -/
def intervalStepMomentNumerator (a b : ℝ) : ℝ :=
  ∫ u in a..b, u

/-- Cost after normalising the interval step to unit mass. -/
def normalizedIntervalStepCost (a b : ℝ) : ℝ :=
  intervalStepCostNumerator a b / intervalStepMass a b

/-- First moment after normalising the interval step to unit mass. -/
def normalizedIntervalStepMoment (a b : ℝ) : ℝ :=
  intervalStepMomentNumerator a b / intervalStepMass a b

/-- The pair carried by a normalised interval step. -/
def normalizedIntervalStepPair (a b : ℝ) : ℝ × ℝ :=
  (normalizedIntervalStepCost a b, normalizedIntervalStepMoment a b)

/-- An interior left endpoint of a superlevel component. -/
def interiorLeftEndpoint (w : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) : Prop :=
  1 < p.1 ∧ w p.1 ≤ t

/-- A left endpoint which is the trace at the left domain boundary. -/
def leftDomainTrace (w : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 = 1 ∧ w 1 > t

/-- An interior right endpoint of a superlevel component. -/
def interiorRightEndpoint (ξ : ℝ) (w : ℝ → ℝ) (t : ℝ)
    (p : ℝ × ℝ) : Prop :=
  p.2 < ξ ∧ w p.2 ≤ t

/-- A right endpoint which is the trace at the right domain boundary. -/
def rightDomainTrace (ξ : ℝ) (w : ℝ → ℝ) (t : ℝ)
    (p : ℝ × ℝ) : Prop :=
  p.2 = ξ ∧ w ξ > t

/-- Claim 2017: the normalised interval-step pair is the displayed
reciprocal/logarithmic cost and midpoint, and the reciprocal endpoint terms
are carried by the endpoint-aware weighted coarea decomposition. -/
def intervalStepCostAndMoment_claim2017 : Prop :=
  (∀ (ξ a b : ℝ),
    1 ≤ a → a < b → b ≤ ξ →
      intervalStepMass a b = b - a ∧
      normalizedIntervalStepPair a b =
        ((a⁻¹ + b⁻¹ + Real.log (b / a)) / (b - a), (a + b) / 2)) ∧
  (∀ (ξ : ℝ) (w : ℝ → ℝ)
      (components : ℝ → Finset (ℝ × ℝ)),
    1 < ξ →
    ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) ξ) →
    (∀ u ∈ Set.Icc (1 : ℝ) ξ, 0 ≤ w u) →
    (∫ u in (1 : ℝ)..ξ, w u) = 1 →
    (∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      isLayerCakeComponentDecomposition w ξ t (components t)) →
    (∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (∀ p ∈ components t,
        (interiorLeftEndpoint w t p ∨ leftDomainTrace w t p) ∧
          (interiorRightEndpoint ξ w t p ∨ rightDomainTrace ξ w t p))) ∧
      w 1 + w ξ / ξ +
          (∫ u in (1 : ℝ)..ξ, |deriv w u| / u) =
        ∫ t,
          (∑ p ∈ components t, (p.1⁻¹ + p.2⁻¹))
            ∂(volume.restrict (Set.Ioi (0 : ℝ))))

end

end MathlibPlus.Open.Analysis.CHJIntervalStep
