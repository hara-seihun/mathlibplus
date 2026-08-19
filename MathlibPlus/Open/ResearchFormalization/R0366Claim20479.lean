import MathlibPlus.Open.Research.R0366Claim20484
import MathlibPlus.Open.Research.R0366Claim20485

namespace MathlibPlus.Open.ResearchFormalization.R0366Claim20479

open MathlibPlus.Open.Research.R0366Claim20484
open MathlibPlus.Open.Research.R0366Claim20485

noncomputable section

/-- The vertex deck together with every dominating ordered-root boundary
profile determines every complete ordered-root profile. -/
def deckAndDominatingRootProfileDeterminesFullProfile_claim20479 : Prop :=
  ∀ (n r : ℕ), 1 ≤ r → r < n →
    ∀ (G H : SimpleGraph (Fin n)),
      vertexDeckEqual G H →
        (∀ A : SimpleGraph (Fin r),
          dominatingRootBoundary G A = dominatingRootBoundary H A) →
          (∀ A : SimpleGraph (Fin r),
            MathlibPlus.Open.Research.R0366Claim20484.profilePolynomial G A =
              MathlibPlus.Open.Research.R0366Claim20484.profilePolynomial H A)

end

end MathlibPlus.Open.ResearchFormalization.R0366Claim20479
