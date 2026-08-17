import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

namespace MathlibPlus.Open.GraphTheory.R1168Claim41556

open MathlibPlus.Open.GraphTheory.R1168

/-- Claim 41556: the standard odd unresolved fiber has a five-dimensional
profile space, represented by its exact cardinality over `ZMod 7`, and every
unresolved profile is precisely a period-two profile. -/
def claim41556 : Prop :=
  Set.Finite standardOddUnresolvedSpace ∧
    Set.ncard standardOddUnresolvedSpace = 7 ^ 5 ∧
    (∀ s : Profile,
      s ∈ standardOddUnresolvedSpace ↔
        ∃ f : ZMod 5 → ZMod 7, s = periodTwoProfile f)

end MathlibPlus.Open.GraphTheory.R1168Claim41556
