import MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

namespace MathlibPlus.Open.ResearchFormalization.R1184Claim41743

noncomputable section

open MathlibPlus.Open.Research.R1184Formalization_41746
open MathlibPlus.Open.ResearchFormalization.R1184.Claim41749

/-- A normal block-chain schedule has prime, nonincreasing successive ratios. -/
def primeNonincreasingSchedule (schedule : List ℕ) : Prop :=
  (∀ q ∈ schedule, Nat.Prime q) ∧
    List.Pairwise (fun a b => a ≥ b) schedule

/-- Claim 41743: an odd square-free regular `E(C_m,8)` pair admits, after
conjugating one copy inside the generated pair, a nested normal block chain;
either its schedule matches an exceptional degree-24 terminal or its ratios
are prime and nonincreasing. -/
def claim41743 : Prop :=
  ∀ (m : ℕ),
    1 < m → Odd m → Squarefree m →
      ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
        Fintype.card Ω = 8 * m →
          ∀ (R T : Subgroup (Equiv.Perm Ω)),
            regularECopy m R → regularECopy m T →
              ∃ g : generatedPair R T,
                ∃ schedule : List ℕ,
                  ∃ chain : List (Set (Set Ω)),
                    normalBlockSchedule
                        (generatedPair R
                          (conjugateSubgroup (g : Equiv.Perm Ω) T))
                        schedule chain ∧
                      ((∃ (n : ℕ) (pre terminal : List ℕ),
                          exceptionalTerminalBranch m n pre terminal ∧
                            schedule = pre ++ terminal) ∨
                        primeNonincreasingSchedule schedule)

end
end MathlibPlus.Open.ResearchFormalization.R1184Claim41743
