import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

namespace MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The exact disconnected Q₁₅₆ recognition Cayley graph statement: inverse
closure, thirteen identical connected quotient components of valency eight,
the 624-edge count, and the selected orbital among the three stated sizes. -/
def claim34418 : Prop :=
  inverseClosed g156S ∧
    disjointQuotientCopies ∧
    connectedRelation quotientAdj ∧
    (∀ h : Q12, relationValency quotientAdj h = 8) ∧
    orderedRelationEdges recognitionAdj = 1248 ∧
    orderedRelationEdges recognitionAdj / 2 = 624 ∧
    Set.ncard q12OrbitalSet = 96 ∧
    selectedOrbital exceptionalAmbient127 = q12OrbitalSet ∧
    selectedOrbital exceptionalAmbient204 = q12OrbitalSet ∧
    orbitalSizes exceptionalAmbient127 = {12, 36, 96} ∧
    orbitalSizes exceptionalAmbient204 = {12, 36, 96}

end MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722
