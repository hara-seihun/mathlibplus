import MathlibPlus.Open.Research.R1184Claim41747
import MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

namespace MathlibPlus.Open.ResearchFormalization.R1184Claim31977

open MathlibPlus.Open.Research.R1184Formalization_41747
open MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

noncomputable section

/-- Claim 31977: in the exact regular-copy normal block-chain carrier, an
    odd square-free `m` not divisible by three cannot have an exceptional
    degree-24 terminal. -/
def threeDoesNotDivideMExcludesExceptionalTerminal_claim31977 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (m n : ℕ) (R T : Subgroup (Equiv.Perm Ω)),
    Odd m → Squarefree m → ¬ 3 ∣ m →
      regularECopy m R → regularECopy m T →
        ∀ g : generatedPair R T,
          ∀ (pre terminal : List ℕ) (chain : List (Set (Set Ω))),
            exceptionalTerminalBranch m n pre terminal →
              normalBlockSchedule
                (generatedPair R
                  (conjugateSubgroup (g : Equiv.Perm Ω) T))
                (pre ++ terminal) chain →
                  False

end

end MathlibPlus.Open.ResearchFormalization.R1184Claim31977
