import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31952

open MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The admitted full automorphism-group description of the recognition graph. -/
def claim31952 : Prop :=
  ∀ f : Equiv.Perm G156,
    relationAutomorphism recognitionAdj f ↔ wreathMember f

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31952
