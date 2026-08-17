import MathlibPlus.Open.ResearchFormalization.R0296ConnectivityScalar

namespace MathlibPlus.Open.ResearchFormalization.R0296ConnectivityWeight

open MathlibPlus.Open.ResearchFormalization.R0296ConnectivityScalar

/-- Claim 19520: the proposed sign-reversing pair has unequal weights in the
free connectivity module throughout the intended range.  Thus the pair cannot
cancel there merely because its scalar augmentations agree. -/
def signReversingInvolutionNotWeightPreserving_claim19520 : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    let w : ℝ := 5 / 4 + s
    literalContact w ≠ zipperTensor w

end MathlibPlus.Open.ResearchFormalization.R0296ConnectivityWeight
