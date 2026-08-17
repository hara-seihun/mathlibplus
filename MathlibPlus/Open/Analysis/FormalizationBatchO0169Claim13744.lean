import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

open scoped BigOperators ComplexConjugate ENNReal
open Filter MeasureTheory Set Topology

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0169Claim13744

noncomputable section

open MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

/-- Fixed-profile critical-zero lower bound, with the real and positive-integer
scale limsups carried by the reviewed Nyman profile definitions. -/
def claim_13744 : Prop :=
  ∀ (w : ℝ → ℝ) (W : ℂ → ℂ) (c : ℝ) (ρ : ℂ),
    MathlibPlus.Open.Analysis.FormalizationBatchMellin.smoothFixedProfile w →
    w ≠ (fun _ : ℝ => 0) →
    profileMellinContinuation w W c →
    criticalLineSimpleZero ρ →
      profileLowerBound ρ W ≤ realErrorLimsup w ∧
        profileLowerBound ρ W ≤ integerErrorLimsup w ∧
        0 < profileLowerBound ρ W

end

end MathlibPlus.Open.Analysis.FormalizationBatchO0169Claim13744
