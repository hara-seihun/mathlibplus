import MathlibPlus.Open.ResearchFormalization.R1368Valency14Histogram

namespace MathlibPlus.Open.ResearchFormalization.R1368Claim38288

open MathlibPlus.Open.ResearchFormalization.R1368Valency14Histogram

/-- Claim 38288: every nonnormal valency-fourteen row has an invariant
proper nontrivial subgroup-coset system on the exact CayleyGroup carrier. -/
def claim38288 : Prop :=
  ∀ S : Connection14, nonnormalRow S →
    ∃ H : AddSubgroup G1368,
      H ∈ invariantCosetSystems1368 S

end MathlibPlus.Open.ResearchFormalization.R1368Claim38288
