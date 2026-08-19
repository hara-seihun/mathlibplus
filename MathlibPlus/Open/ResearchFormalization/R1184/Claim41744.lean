import MathlibPlus.Open.Research.R1184Claim41746
import MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

namespace MathlibPlus.Open.ResearchFormalization.R1184.Claim41744

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41746
open MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

/-- Claim 41744: in the normal block-chain reduction for two regular copies of
`E(C_m,8)`, an exceptional degree-24 terminal branch cannot occur when `m` is
odd, square-free, and not divisible by three.  The recursive exceptional
branch itself retains the exact equation `m = 3*n`, its prefix scale, and one
of the three displayed terminal schedules. -/
def claim41744 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
    ∀ (m n : ℕ) (R T : Subgroup (Perm Ω)),
      Odd m →
        Squarefree m →
          ¬ 3 ∣ m →
            regularECopy m R →
              regularECopy m T →
                ∀ g : generatedPair R T,
                  ∀ (pre terminal : List ℕ)
                    (chain : List (Set (Set Ω))),
                    exceptionalTerminalBranch m n pre terminal →
                      normalBlockSchedule
                        (generatedPair R
                          (conjugateSubgroup (g : Perm Ω) T))
                        (pre ++ terminal) chain →
                        False

end

end MathlibPlus.Open.ResearchFormalization.R1184.Claim41744
