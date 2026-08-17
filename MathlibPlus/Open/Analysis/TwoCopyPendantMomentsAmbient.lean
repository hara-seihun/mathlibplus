import Mathlib
import MathlibPlus.Open.Analysis.TwoCopyPendantMoments

namespace MathlibPlus.Open.Analysis.TwoCopyPendantMoments

noncomputable section

/-- Claim 24922: among valid selected depth-five profile flows, a nonzero
split-off-one divergence can have zero two-copy pendant specialization. -/
def ambientTwoCopyNonvanishingIsFalse : Prop :=
  ¬ ∀ α : ProfileFlow,
      IsDepthFiveProfileFlow α →
        profileDivergence α ≠ 0 →
          twoCopySpecialization (profileDivergence α) ≠ 0

end

end MathlibPlus.Open.Analysis.TwoCopyPendantMoments
