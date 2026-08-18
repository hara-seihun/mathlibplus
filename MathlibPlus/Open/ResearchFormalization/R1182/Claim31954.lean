import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31954

open MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The admitted fiberwise nonlinear full graph automorphism statement. -/
def claim31954 : Prop :=
  relationAutomorphism recognitionAdj nu ∧
    commonBlockPreserving nu ∧
    (∀ c : ZMod 13, ∀ v : Q12,
      coordinateChart (nu (coordinateChart (c, v))) =
        (q156Chi v * rho (q156Chi v * c), v)) ∧
    (∀ v : Q12,
      ¬affineOverF13 (fun x : ZMod 13 =>
        q156Chi v * rho (q156Chi v * x)))

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31954
