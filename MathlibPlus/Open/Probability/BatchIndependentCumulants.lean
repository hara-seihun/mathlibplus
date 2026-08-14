import Mathlib

namespace MathlibPlus.Open.Probability.IndependentCumulants

noncomputable section

/-- Local existence of the two moment-generating functions on one neighborhood
of the origin. -/
def mgfNeighborhood {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ t : ℝ, ‖t‖ < ε →
      MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) μ ∧
        MeasureTheory.Integrable (fun ω => Real.exp (t * Y ω)) μ

/-- Claim 9278: independence makes the joint cumulant-generating function
factor into the two one-variable functions. -/
def cumulantGeneratingFunctionFactorization : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X Y : Ω → ℝ),
    Measurable X → Measurable Y → ProbabilityTheory.IndepFun X Y μ →
    mgfNeighborhood μ X Y →
      ∀ {ε : ℝ},
        (0 < ε) →
        (∀ t : ℝ, ‖t‖ < ε →
          MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) μ ∧
            MeasureTheory.Integrable (fun ω => Real.exp (t * Y ω)) μ) →
        ∀ t u : ℝ, ‖t‖ < ε → ‖u‖ < ε →
          Real.log (∫ ω, Real.exp (t * X ω + u * Y ω) ∂μ) =
            Real.log (∫ ω, Real.exp (t * X ω) ∂μ) +
              Real.log (∫ ω, Real.exp (u * Y ω) ∂μ)

end
end MathlibPlus.Open.Probability.IndependentCumulants
