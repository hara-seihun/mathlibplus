import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654.Claim42193

open MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

def twoLehmerTargetTypeIVWitnesses_claim42193 : Prop :=
  ∃ (A₁ Astar₁ R₁ P₁₁ P₂₁ q₁ r₁
      A₂ Astar₂ R₂ P₁₂ P₂₂ q₂ r₂ : Polynomial ℤ),
    genuineTypeIVWitness 5 lehmerTarget A₁ Astar₁ R₁ P₁₁ P₂₁ q₁ r₁
      firstCorrection ∧
      genuineTypeIVWitness 5 lehmerTarget A₂ Astar₂ R₂ P₁₂ P₂₂ q₂ r₂
        secondCorrection

end MathlibPlus.Open.ResearchFormalization.R2654.Claim42193
