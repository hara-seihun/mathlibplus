import MathlibPlus.Open.Research.R1468

namespace MathlibPlus.Open.ResearchFormalization.R1368Valency14OrbitGraphCounts

noncomputable section

open MathlibPlus.Open.Research.R1468

abbrev G1368 := CayleyGroup
abbrev Connection14 := ConnectionSet 14
abbrev PresentationOrbit1368 := Quotient (presentationSetoid 14)
abbrev GraphType1368 := Quotient (graphSetoid 14)

/-- Claim 38281: the exact valency-fourteen presentation-orbit and ordinary
graph-isomorphism quotients have the same cardinality, and graph equivalence
is exactly equivalence under an automorphism of the retained Cayley group. -/
def claim38281 : Prop :=
  (letI := Fintype.ofFinite PresentationOrbit1368
   Fintype.card PresentationOrbit1368 = 11396) ∧
  (letI := Fintype.ofFinite GraphType1368
   Fintype.card GraphType1368 = 11396) ∧
  (∀ S T : Connection14,
    graphEquivalent S T ↔ automorphismEquivalent S T)

end

end MathlibPlus.Open.ResearchFormalization.R1368Valency14OrbitGraphCounts
