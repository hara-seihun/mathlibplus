import Mathlib

open MeasureTheory Asymptotics Filter

namespace MathlibPlus.Open.ProjectsResearch.O0064Measure

/-- A positive cosine-measure representation has a finite quadratic moment when
    its represented wave kernel is smooth at the origin, with the forced
    nonpositive quadratic coefficient. -/
def claim12767_positiveScalarCosineMeasureMoment : Prop :=
  ∀ (μ : Measure ℝ),
    μ (Set.Iio (0 : ℝ)) = 0 →
      let k : ℝ → ℝ := fun u => ∫ ξ : ℝ, Real.cos (ξ * u) ∂μ
      ContDiffAt ℝ ⊤ k 0 →
        Integrable (fun ξ : ℝ => ξ ^ 2) μ ∧
          ∃ c0 c2 : ℝ,
            c0 = k 0 ∧
              IsBigO (nhds 0)
                (fun u : ℝ => k u - c0 - c2 * u ^ 2)
                (fun u : ℝ => |u| ^ 4) ∧
              c2 = -(1 / 2) * (∫ ξ : ℝ, ξ ^ 2 ∂μ) ∧
              c2 ≤ 0

end MathlibPlus.Open.ProjectsResearch.O0064Measure
