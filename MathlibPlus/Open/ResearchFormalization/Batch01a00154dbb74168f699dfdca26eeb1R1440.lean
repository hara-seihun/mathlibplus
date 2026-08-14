import MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1R1440

abbrev R1440GL53 :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R1440GL53

abbrev R1440SubgroupConjugacySetoid :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r1440SubgroupConjugacySetoid

abbrev R1440ClassesWithAtLeastNineFixedVectors :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r1440ClassesWithAtLeastNineFixedVectors

/-- Exact source-subgroup and fixed-plane census for the fixed Sylow subgroup `P`. -/
def r1440ExactSourceSubgroupFixedPlaneCensus
    (P : Sylow 3 R1440GL53) : Prop :=
  Nat.card (Quotient (R1440SubgroupConjugacySetoid P)) = 56251 ∧
    Nat.card (R1440ClassesWithAtLeastNineFixedVectors P) = 28417

end MathlibPlus.Open.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1R1440
