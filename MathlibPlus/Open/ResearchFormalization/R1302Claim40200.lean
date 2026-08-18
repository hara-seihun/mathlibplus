import MathlibPlus.Open.ResearchFormalization.R1302Claim40201

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40200

open MathlibPlus.Open.ResearchFormalization.R1302Claim40197
open MathlibPlus.Open.ResearchFormalization.R1302Claim40201

/-- Claim 40200: in the exact pure-C4 row, two allowed conjugations produce
    a three-block size-28 coarsening and then equality of the twelve-block
    characteristic-seven orbit partitions. -/
def claim40200 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
    Fintype.card Ω = 84 →
      ∀ (B : Finset (Set Ω))
        (R T X : Subgroup (Equiv.Perm Ω)),
        pureC4Row B R T X →
          ∃ P Q : Subgroup (Equiv.Perm Ω),
            isO7 R P ∧
              isO7 T Q ∧
                ∃ x : X,
                  let Tx :=
                    conjugateSubgroup (x : Equiv.Perm Ω) T
                  let Hx := generatedPair R Tx
                  ∃ C : Set (Set Ω),
                    threeBlockCoarsening B C ∧
                      preservesBlockFamily Hx C ∧
                        ∃ k : Hx,
                          inCoarseBlockKernel C k ∧
                            twelveSevenOrbitPartition P
                              (conjugateSubgroup
                                ((x : Equiv.Perm Ω) *
                                  (k : Equiv.Perm Ω)) Q)

end MathlibPlus.Open.ResearchFormalization.R1302Claim40200
