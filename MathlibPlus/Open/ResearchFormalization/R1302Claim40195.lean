import MathlibPlus.Open.ResearchFormalization.R1302Claim40201

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40195

open MathlibPlus.Open.ResearchFormalization.R1302Claim40196
open MathlibPlus.Open.ResearchFormalization.R1302Claim40197
open MathlibPlus.Open.ResearchFormalization.R1302Claim40201

noncomputable section

/-- No nonidentity element of a seven-subgroup fixes a displayed four-point
block under the actual block-action homomorphism. -/
def noNonidentityBlockFixing {Ω : Type*}
    (B : Finset (Set Ω))
    (H P : Subgroup (Equiv.Perm Ω))
    (hP : P ≤ H)
    (ρ : H →* BlockPerm B) : Prop :=
  ∀ p : P, p ≠ 1 →
    ∀ U : BlockPoint B,
      ρ ⟨(p : Equiv.Perm Ω), hP p.property⟩ U ≠ U

/-- Claim 40195: in the exact pure-`C₄` setup, the characteristic order-seven
subgroups of the two regular copies have order seven, have no fixed original
block, and induce semiregular order-seven actions with three seven-point
orbits on the 21 displayed blocks. -/
def claim40195 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
    Fintype.card Ω = 84 →
      ∀ (B : Finset (Set Ω))
        (R T X : Subgroup (Equiv.Perm Ω)),
        ∀ data : PureC4Data B R T X,
          ∃ P Q : Subgroup (Equiv.Perm Ω),
            ∃ hP : isO7 R P,
              ∃ hQ : isO7 T Q,
                Nat.card P = 7 ∧
                  Nat.card Q = 7 ∧
                    noNonidentityBlockFixing B R P hP.1 data.rhoR ∧
                      noNonidentityBlockFixing B T Q hQ.1 data.rhoT ∧
                        let Pbar :=
                          inducedImage P R hP.1 B data.rhoR
                        let Qbar :=
                          inducedImage Q T hQ.1 B data.rhoT
                        orderSevenWithThreeOrbits Pbar ∧
                          orderSevenWithThreeOrbits Qbar

end
end MathlibPlus.Open.ResearchFormalization.R1302Claim40195
