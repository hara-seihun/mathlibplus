import MathlibPlus.Open.Research.FormalizationBatch01a000eb.O0319

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.O0319

/-- The first-harmonic contribution of a selected zero at the evaluation point
`σ + iT`, using the shifted resolvent from the positive-mixture packet. -/
def targetZeroFirstHarmonic (μ : ShiftMeasure) (a₁ σ T : ℝ) (ρ₀ : ℂ) : ℂ :=
  -(a₁ : ℂ) *
    shiftResolvent μ ((σ : ℂ) + Complex.I * (T : ℂ) - ρ₀)

/-- Claim 14169: a target zero contributes the negative first-harmonic
resolvent value, whose magnitude is bounded by endpoint mass. -/
def claim14169 : Prop :=
  ∀ μ : ShiftMeasure, positiveFiniteMeasure μ →
    ∀ a₁ σ β T δ : ℝ, 0 < a₁ → 0 < δ → δ = σ - β →
      ∀ ρ₀ : ℂ,
        riemannZeta ρ₀ = 0 →
          ρ₀ = (β : ℂ) + (T : ℂ) * Complex.I →
            targetZeroFirstHarmonic μ a₁ σ T ρ₀ =
                -(a₁ : ℂ) * shiftResolvent μ (δ : ℂ) ∧
              ‖targetZeroFirstHarmonic μ a₁ σ T ρ₀‖ ≤
                a₁ * Measure.real μ Set.univ / δ

end MathlibPlus.Open.ResearchFormalization.O0319
