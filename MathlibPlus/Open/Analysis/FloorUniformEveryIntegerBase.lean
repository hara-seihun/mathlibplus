import MathlibPlus.Open.Analysis.LargeBaseFiberFloor

namespace MathlibPlus.Open.Analysis

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The exact measurable periodic relaxation defining the O-0313 fiber distance. -/
noncomputable def o0313PeriodicFiberDistance (q : ℕ) : ℝ :=
  sInf {v : ℝ |
    ∃ g : ℝ → ℂ,
      Measurable g ∧
        Function.Periodic g (fiberPeriod q) ∧
          v = ∫ t : ℝ,
            ‖g t * criticalBase q t - 1‖ ^ 2 ∂criticalCauchyMeasure}

/-- The infimum of the exact periodic-fiber distances over integer bases. -/
noncomputable def o0313IntegerBaseDistanceInfimum : ℝ :=
  sInf {v : ℝ | ∃ q : ℕ, 2 ≤ q ∧ v = o0313PeriodicFiberDistance q}

/-- Fixed-base positivity and the positive large-base limit give a uniform floor. -/
def floorUniformOverEveryIntegerBase : Prop :=
  0 < o0313IntegerBaseDistanceInfimum

end

end MathlibPlus.Open.Analysis
