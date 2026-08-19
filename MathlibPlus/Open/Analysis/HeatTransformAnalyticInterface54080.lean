import MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

open MeasureTheory

namespace MathlibPlus.Open.Analysis.HeatTransformAnalyticInterface54080

noncomputable section

open MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

/-- The iterated time derivative at the origin in the complex space variable. -/
noncomputable def originTimeDerivative
    (μ : Measure ℝ) (τ : ℝ) (k : ℕ) : ℂ :=
  iteratedDeriv k (fun s : ℝ => heatTransform μ s 0) τ

/-- The backward heat equation written with the real time derivative and the
complex second space derivative. -/
def backwardHeatEquation
    (μ : Measure ℝ) (t : ℝ) (z : ℂ) : Prop :=
  HasDerivAt
    (fun s : ℝ => heatTransform μ s z)
    (-deriv (fun w : ℂ => deriv (heatTransform μ t) w) z) t

/--
R-4946.2 (claim 54080): a positive even discrete source with the admitted
super-exponential tail condition has an entire heat transform in its complex
space variable, all origin-time jets have the displayed integral values, and
the transform satisfies the backward heat equation.
-/
def claim_54080 : Prop :=
  ∀ μ : Measure ℝ,
    PositiveEvenDiscreteSuperexponential μ →
      (∀ t : ℝ, Differentiable ℂ (heatTransform μ t)) ∧
      (∀ (τ : ℝ) (k : ℕ),
        originTimeDerivative μ τ k = originJet μ τ k) ∧
      (∀ (t : ℝ) (z : ℂ), backwardHeatEquation μ t z)

end

end MathlibPlus.Open.Analysis.HeatTransformAnalyticInterface54080
