import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31953

open MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The admitted exceptional regular `Q₁₅₆` lifts, with the quotient copies
required to lie in their stated exceptional ambient groups. -/
def claim31953 : Prop :=
  Nat.card exceptionalAmbient127 = 288 ∧
    exceptionalLiftPair exceptionalAmbient127 0 1 ∧
      Nat.card exceptionalAmbient204 = 1152 ∧
        exceptionalLiftPair exceptionalAmbient204 0 1 ∧
          exceptionalLiftPair exceptionalAmbient204 0 2 ∧
            exceptionalLiftPair exceptionalAmbient204 1 2

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31953
