import Mathlib
import MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557
import MathlibPlus.Open.ResearchFormalization.Batch

open scoped BigOperators
open MeasureTheory Set

namespace MathlibPlus.Open.Analysis.ResearchFormalizationClaim15560

noncomputable section

/-- The exact completed carrier produced by the one-sided shift measure: the
 shift acts through its genuine Laplace transform, rather than through an
 unconstrained multiplier. -/
def shiftedCompletedCarrier
    (μ : SignedMeasure (Set.Ici (0 : ℝ))) (ν : Measure ℝ) : Prop :=
  MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557.exactCompletedMixedCarrier
    (MathlibPlus.Open.ResearchFormalization.Batch.oneSidedLaplaceTransform μ) ν

/-- Claim 15560: no finite real signed measure on the one-sided carrier can
 produce a locally finite nonnegative exact completed mixed carrier through
 the shift/Laplace interchange. -/
def noNonzeroFiniteOneSidedShiftMeasure_claim15560 : Prop :=
  ∀ μ : SignedMeasure (Set.Ici (0 : ℝ)),
    MathlibPlus.Open.ResearchFormalization.Batch.FiniteOneSidedSignedMeasure μ →
      (∃ ν : Measure ℝ, shiftedCompletedCarrier μ ν) →
        μ = 0

end

end MathlibPlus.Open.Analysis.ResearchFormalizationClaim15560
