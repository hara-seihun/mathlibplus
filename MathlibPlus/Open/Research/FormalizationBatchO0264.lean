import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchO0264

noncomputable section

open scoped BigOperators
open Filter
open MeasureTheory

/-- The explicit hypotheses carried by a certified simple critical zero. -/
def certifiedSimpleCriticalZero (ρ : ℂ) : Prop :=
  ρ.re = (1 / 2 : ℝ) ∧
    riemannZeta ρ = 0 ∧
      deriv riemannZeta ρ ≠ 0 ∧ ρ ≠ 0

/-- The normalized packet away from its removable center. -/
noncomputable def rawCriticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  riemannZeta (ρ + Complex.I * (y : ℂ)) *
      Complex.Gamma (-Complex.I * (y : ℂ)) /
    ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)

/-- The normalized packet with its removable value at zero. -/
noncomputable def criticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  if y = 0 then -(1 : ℂ) / ρ else rawCriticalZeroPacket ρ y

/-- The positive packet-energy constant. -/
noncomputable def packetEnergyConstant (ρ : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖criticalZeroPacket ρ y‖ ^ 2

/-- The Fourier multiplier of a finite complex scale measure. -/
noncomputable def complexMeasureMultiplier
    (N : ℝ) (μ : MeasureTheory.ComplexMeasure ℝ) (y : ℝ) : ℂ :=
  ∫ᵛ x, Complex.exp
      (-Complex.I * (x : ℂ) * (y : ℂ) * (Real.log N : ℂ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- The packet energy after applying a scale-measure multiplier. -/
noncomputable def pointSupportedPacketEnergy
    (ρ : ℂ) (N : ℝ) (μ : MeasureTheory.ComplexMeasure ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ,
      ‖criticalZeroPacket ρ y * complexMeasureMultiplier N μ y‖ ^ 2

/-- Claim 15094: a point-supported mass-one mixture has fixed packet energy. -/
def claim_15094 : Prop :=
  ∀ (ρ : ℂ) (N c : ℝ) (μ : MeasureTheory.ComplexMeasure ℝ),
    certifiedSimpleCriticalZero ρ →
    N > 1 →
    IsFiniteMeasure (VectorMeasure.variation μ) →
    μ Set.univ = 1 →
    μ ({c}ᶜ) = 0 →
      (∀ y : ℝ,
        complexMeasureMultiplier N μ y =
          Complex.exp
            (-Complex.I * (c : ℂ) * (y : ℂ) * (Real.log N : ℂ))) ∧
        let Cρ := packetEnergyConstant ρ
        Cρ > 0 ∧ pointSupportedPacketEnergy ρ N μ = Cρ

end

end MathlibPlus.Open.Research.FormalizationBatchO0264
