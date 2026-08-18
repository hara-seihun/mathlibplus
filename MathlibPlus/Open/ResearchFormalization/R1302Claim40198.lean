import MathlibPlus.Open.ResearchFormalization.R1302Claim40201

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40198

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1302Claim40197
open MathlibPlus.Open.ResearchFormalization.R1302Claim40201

/-- The mixed row on the first coarsening, with the order of the copy-kernel
intersection made explicit. -/
def mixedC7C4RowWithOrder40198
    {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (C : Set (Set Ω)) : Prop :=
  ∃ K : Subgroup H,
    familyKernelCorrect H C K ∧
      ∀ D ∈ C, ∃ S : Subgroup H,
        blockStabilizerCorrect H D S ∧
          Nonempty (C7C4 ≃* S) ∧
            Nonempty (C7C2 ≃* (S ⊓ K : Subgroup H)) ∧
              Nat.card (S ⊓ K : Subgroup H) = 14

/-- Claim 40198: the first three-part coarsening of the pure `C₄` row has
28-point blocks whose stabilizers in both aligned regular copies are
`C₇ × C₄`; the intersection with the actual action kernel on that coarsening
is `C₇ × C₂` and has order 14. -/
def claim40198 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω],
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
                        mixedC7C4RowWithOrder40198 R C ∧
                          mixedC7C4RowWithOrder40198 Tx C ∧
                            fixesEveryCoarseBlock P C ∧
                              fixesEveryCoarseBlock
                                (conjugateSubgroup (x : Equiv.Perm Ω) Q) C

end

end MathlibPlus.Open.ResearchFormalization.R1302Claim40198
