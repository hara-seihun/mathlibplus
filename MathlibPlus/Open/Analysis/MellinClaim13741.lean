import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchMellin
import MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

namespace MathlibPlus.Open.Analysis.FormalizationBatchMellinClaim13741

open MathlibPlus.Open.Analysis.FormalizationBatchMellin
open MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

/-- Every smooth fixed profile has the meromorphic Mellin continuation with
its profile coefficient, analytic remainder, pole normalization, and rapid
vertical decay. -/
def claim13741_fixedProfileMellinContinuation : Prop :=
  ∀ w : ℝ → ℝ,
    smoothFixedProfile w →
      ∃ c : ℝ, ∃ W : ℂ → ℂ,
        profileMellinContinuation w W c

end MathlibPlus.Open.Analysis.FormalizationBatchMellinClaim13741
