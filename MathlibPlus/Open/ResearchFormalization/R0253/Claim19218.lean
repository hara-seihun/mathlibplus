import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchR0253

namespace MathlibPlus.Open.ResearchFormalization.R0253.Claim19218

open MeasureTheory
open scoped ENNReal

/-- The exact two-atom measure is anchored in the statement itself, while the
reviewed divided-even-moment carrier supplies the `(2j)!` divisor.  The three
source values are retained for every measure equal to that literal atom sum. -/
def exactTwoAtomDividedMoments : Prop :=
  ∀ μ : Measure ℝ,
    μ = (Measure.dirac (0 : ℝ) +
      (1 / 100 : ℝ≥0∞) • Measure.dirac (10 : ℝ)) →
    MathlibPlus.Open.Research.FormalizationBatchR0253.dividedEvenMoment μ 0 =
        (101 : ℝ) / 100 ∧
      MathlibPlus.Open.Research.FormalizationBatchR0253.dividedEvenMoment μ 1 =
        (1 : ℝ) / 2 ∧
      MathlibPlus.Open.Research.FormalizationBatchR0253.dividedEvenMoment μ 2 =
        (25 : ℝ) / 6

end MathlibPlus.Open.ResearchFormalization.R0253.Claim19218
