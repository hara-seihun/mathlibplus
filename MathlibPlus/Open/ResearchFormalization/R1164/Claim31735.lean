import MathlibPlus.Open.ResearchFormalization.R1164FullSuborbit

namespace MathlibPlus.Open.ResearchFormalization.R1164.Claim31735

open MathlibPlus.Open.ResearchFormalization.R1164

def generatedGroupAndSuborbitDistribution_claim31735 : Prop :=
  r1164RetainedCount = 50262 ∧
    r1164CensusClassCount (3 ^ 9) 81 1 = 7062 ∧
      r1164CensusClassCount (3 ^ 11) 73 1 = 11520 ∧
        r1164CensusClassCount (3 ^ 11) 61 2 = 31680 ∧
          r1164ImageRankCount 1 = 18582 ∧
            r1164ImageRankCount 2 = 31680 ∧
              r1164CensusClassCount (3 ^ 9) 81 1 +
                  r1164CensusClassCount (3 ^ 11) 73 1 +
                    r1164CensusClassCount (3 ^ 11) 61 2 =
                r1164RetainedCount ∧
                ∀ r : R1164RetainedRow,
                  r1164DisplayedClosureFailure r

end MathlibPlus.Open.ResearchFormalization.R1164.Claim31735
