import MathlibPlus.Analysis.LogarithmicTranslation

namespace MathlibPlus.Open.Analysis

open MeasureTheory

/-- Exact expanding-interval packet defect for logarithmic translation. -/
def expandingIntervalPacketDefect_claim9813 : Prop :=
  ∀ (a θ r : ℝ) (z : ℂ) (R : ℝ),
    a ≠ 0 →
    0 ≤ r →
    z = (r : ℂ) * Complex.exp (Complex.I * θ) →
    R > |a| / 2 →
    ∃ f_R : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂(volume : Measure ℝ),
        (f_R : ℝ → ℂ) x =
          ((Real.rpow (2 * R) (-1 / 2 : ℝ)) : ℂ) *
            Complex.exp (Complex.I * (θ * x / a)) *
            Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => (1 : ℂ)) x) ∧
      ‖f_R‖ = 1 ∧
      ‖MathlibPlus.Analysis.LogarithmicTranslation.logarithmicTranslation a f_R -
          z • f_R‖ ^ 2 =
        (r - 1) ^ 2 + |a| * r / R

end MathlibPlus.Open.Analysis
