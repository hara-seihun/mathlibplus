import MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19831

open MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

noncomputable section

def sideProductInjectivity_claim19831 : Prop :=
  ∀ (A B : LegFamily),
    positiveLegFamily A →
      positiveLegFamily B →
        (sideUResponse A = sideUResponse B →
          legMultiset A = legMultiset B) ∧
          (sideSResponse A = sideSResponse B →
            legMultiset A = legMultiset B)

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19831
