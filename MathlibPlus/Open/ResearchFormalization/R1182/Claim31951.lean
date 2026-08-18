import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31951

open MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The admitted disconnected `Q₁₅₆` recognition graph statement. -/
def claim31951 : Prop :=
  inverseClosed g156S ∧
    disjointQuotientCopies ∧
    connectedRelation quotientAdj ∧
    (∀ h : Q12, relationValency quotientAdj h = 8) ∧
    orderedRelationEdges recognitionAdj / 2 = 624 ∧
    Set.ncard q12OrbitalSet = 96 ∧
    selectedOrbital exceptionalAmbient127 = q12OrbitalSet ∧
    selectedOrbital exceptionalAmbient204 = q12OrbitalSet ∧
    orbitalSizes exceptionalAmbient127 = {12, 36, 96} ∧
    orbitalSizes exceptionalAmbient204 = {12, 36, 96}

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31951
