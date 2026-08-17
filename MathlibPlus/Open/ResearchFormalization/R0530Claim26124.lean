import MathlibPlus.Algebra.FiniteDifferenceNormalization

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26124

open MathlibPlus.Algebra.Claim26113
open Polynomial

/-- Claim 26124: adjoining a unit leg to a finite leg multiset has the two
    exact normalized-polynomial update identities. -/
def unitLegAugmentationIdentities_claim26124 : Prop :=
  ∀ (C : Multiset ℕ),
    jPolynomial (C + ({1} : Multiset ℕ)) =
        (1 + Polynomial.X) * jPolynomial C + Polynomial.X ∧
      theta (C + ({1} : Multiset ℕ)) =
        theta C + Polynomial.X * jPolynomial C + Polynomial.X +
          Polynomial.X ^ 2

end MathlibPlus.Open.ResearchFormalization.R0530Claim26124
