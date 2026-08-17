import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0046Claim7836

noncomputable section

/-- The weighted-measure, polynomial-integrability, and two-sided boundary
context used for sufficient decay and integration by parts. -/
def ghsDecayContext (Q : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ) : Prop :=
  0 < Z ∧
    μ = Measure.withDensity volume
      (fun x : ℝ => ENNReal.ofReal (Z⁻¹ * Real.exp (-Q x))) ∧
    IsProbabilityMeasure μ ∧
    Measure.map (fun x : ℝ => -x) μ = μ ∧
    (∀ r : Polynomial ℝ, Integrable (fun x : ℝ => r.eval x) μ) ∧
    (∀ r : Polynomial ℝ,
      Integrable (fun x : ℝ => deriv Q x * r.eval x) μ ∧
      Filter.Tendsto
        (fun x : ℝ => r.eval x * Real.exp (-Q x))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun x : ℝ => r.eval x * Real.exp (-Q x))
        Filter.atBot (nhds 0))

/-- The exact global `C³`, evenness, and positive-half-line curvature
hypotheses. -/
def ghsCurvatureHypotheses (Q : ℝ → ℝ) : Prop :=
  ContDiff ℝ 3 Q ∧
    (∀ x : ℝ, 0 < x → 0 < deriv (deriv Q) x) ∧
    (∀ x : ℝ, 0 < x → deriv (deriv (deriv Q)) x ≤ 0) ∧
    (∀ x : ℝ, Q (-x) = Q x)

/-- Claim 7836: on the exact GHS/Freud carrier, the curvature assumptions
imply positivity and strict increase of `Q'` on the positive half-line and
monotone decrease of `Q''`. -/
def claim7836 : Prop :=
  ∀ (Q : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ),
    ghsDecayContext Q Z μ →
      ghsCurvatureHypotheses Q →
        (∀ x : ℝ, 0 < x → 0 < deriv Q x) ∧
        StrictMonoOn (deriv Q) (Set.Ioi (0 : ℝ)) ∧
        AntitoneOn (deriv (deriv Q)) (Set.Ioi (0 : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.K0046Claim7836
