import MathlibPlus.Open.ResearchFormalization.R1137Claim30117
import MathlibPlus.Open.ResearchFormalization.R1137Claim35025

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim30118

open MathlibPlus.Open.ResearchFormalization.R1137Claim30117
open MathlibPlus.Open.ResearchFormalization.R1137Claim35025

noncomputable section

/-- Claim 30118: the retained normalized affine lifts over the explicit
`12T90` A₄ carrier are harmless for ordinary undirected CI. -/
def allPrimeAffineA4LiftCollapse_claim30118 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (f : R1137Claim30117.PrimeProduct p →
        R1137Claim30117.PrimeProduct p),
      R1137Claim30117.normalizedCommonFibrewiseAffineLift p f →
        ∀ (S : Set (R1137Claim30117.PrimeProduct p)),
          productInverseClosed S →
            productInverseClosed (Set.image f S) →
              productCayleyGraphIsomorphism S (Set.image f S) f →
                ∃ β : R1137Claim30117.PrimeProduct p →
                    R1137Claim30117.PrimeProduct p,
                  productGroupAutomorphism β ∧
                    Set.image β S = Set.image f S

end

end MathlibPlus.Open.ResearchFormalization.R1137Claim30118
