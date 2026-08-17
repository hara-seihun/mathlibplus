import MathlibPlus.Open.ResearchFormalization.R0521Claim22281
import MathlibPlus.Open.ResearchFormalization.ZeroMotion

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22280

open MathlibPlus.Open.ResearchFormalization.R0521Claim22281
open MathlibPlus.Open.ResearchFormalization.ZeroMotion

noncomputable section

/-- Claim 22280: on the reviewed zero-motion trajectory, the derivative of
    each zero is the exact symmetric principal-value interaction of the
    bi-infinite increasing configuration. -/
def deBruijnNewmanZeroMotion_claim22280 : Prop :=
  ∀ (x : ℝ → ℤ → ℝ) (t : ℝ),
    zeroMotionTrajectory x ∧ zeroConfiguration (x t) →
      ∀ i : ℤ, ∃ s : ℝ,
        symmetricPrimedInteraction (x t) i s ∧
          HasDerivAt (fun r : ℝ => x r i) (2 * s) t

end

end MathlibPlus.Open.ResearchFormalization.R0521Claim22280
