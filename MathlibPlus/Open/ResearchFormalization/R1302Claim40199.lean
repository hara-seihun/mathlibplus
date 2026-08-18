import MathlibPlus.Open.ResearchFormalization.R1302Claim40201

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40199

abbrev OrbitSubgroup (Ω : Type*) := Subgroup (Equiv.Perm Ω)

/-- The kernel of the action of `H` on the displayed coarse family `C`,
represented as an ambient permutation subgroup. -/
def coarseActionKernel {Ω : Type*}
    (H : OrbitSubgroup Ω)
    (C : Set (Set Ω))
    (K : OrbitSubgroup Ω) : Prop :=
  K ≤ H ∧
    ∀ h : H, (h : Equiv.Perm Ω) ∈ K ↔
      ∀ D ∈ C, (h : Equiv.Perm Ω) '' D = D

/-- Every orbit of `H` is contained in one displayed coarse block. -/
def orbitsInsideCoarseBlocks {Ω : Type*}
    (H : OrbitSubgroup Ω)
    (C : Set (Set Ω)) : Prop :=
  ∀ u : Ω, ∃ D : Set Ω, D ∈ C ∧
    MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf H u ⊆ D

/-- The seven-point orbit of `P` contained in each indicated `W`-orbit. -/
def containsSevenPointOrbit {Ω : Type*}
    (P W : OrbitSubgroup Ω) : Prop :=
  ∀ u : Ω, ∃ v : Ω,
    MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf P v ⊆
        MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf W u ∧
      (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf P v).ncard = 7

/-- Every indicated orbit has a seven-power cardinality. -/
def sevenPowerOrbitSizes {Ω : Type*}
    (H : OrbitSubgroup Ω) : Prop :=
  ∀ u : Ω, ∃ n : ℕ,
    (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf H u).ncard = 7 ^ n

/-- The strict seven-power orbit squeeze at the size-28 level. -/
def coarseSevenOrbitSqueeze {Ω : Type*}
    (H : OrbitSubgroup Ω)
    (C : Set (Set Ω)) : Prop :=
  orbitsInsideCoarseBlocks H C ∧
    sevenPowerOrbitSizes H ∧
      (28 : ℕ) < 49 ∧
        (∀ n : ℕ, 7 < 7 ^ n → 49 ≤ 7 ^ n) ∧
          (∀ u : Ω,
            7 ≤
              (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf H u).ncard) ∧
            (∀ u : Ω,
              (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitOf H u).ncard = 7)

/-- Equality of the three final orbit partitions, with their exact number and
size of blocks. -/
def commonTwelveSevenOrbitPartition {Ω : Type*}
    (P W Q : OrbitSubgroup Ω) : Prop :=
  MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P =
      MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition W ∧
    MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition W =
      MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition Q ∧
      (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P).ncard = 12 ∧
        ∀ D ∈ MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P,
          D.ncard = 7

/-- Claim 40199: after the first pure-`C₄` coarsening, the kernel Sylow-seven
squeeze supplies a second kernel conjugator and twelve common seven-point
orbit blocks. -/
def claim40199 : Prop :=
  Fintype.card MathlibPlus.Open.ResearchFormalization.R1302Claim40197.Q12 = 12 ∧
    Fintype.card MathlibPlus.Open.ResearchFormalization.R1302Claim40197.G84 = 84 ∧
      MathlibPlus.Open.ResearchFormalization.R1302Claim40201.displayedQ12Presentation ∧
        ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
          Fintype.card Ω = 84 →
            ∀ (B : Finset (Set Ω))
              (R T X : Subgroup (Equiv.Perm Ω)),
              MathlibPlus.Open.ResearchFormalization.R1302Claim40201.pureC4Row B R T X →
                ∃ P Q : Subgroup (Equiv.Perm Ω),
                  MathlibPlus.Open.ResearchFormalization.R1302Claim40197.isO7 R P ∧
                    MathlibPlus.Open.ResearchFormalization.R1302Claim40197.isO7 T Q ∧
                      Nat.card P = 7 ∧
                        Nat.card Q = 7 ∧
                          ∃ x : X,
                            let Tx :=
                              MathlibPlus.Open.ResearchFormalization.R1302Claim40196.conjugateSubgroup
                                (x : Equiv.Perm Ω) T
                            let Hx :=
                              MathlibPlus.Open.ResearchFormalization.R1302Claim40197.generatedPair R Tx
                            ∃ C : Set (Set Ω),
                              MathlibPlus.Open.ResearchFormalization.R1302Claim40197.threeBlockCoarsening
                                  B C ∧
                                MathlibPlus.Open.ResearchFormalization.R1302Claim40201.preservesBlockFamily
                                  Hx C ∧
                                  MathlibPlus.Open.ResearchFormalization.R1302Claim40201.mixedC7C4Row
                                    R C ∧
                                    MathlibPlus.Open.ResearchFormalization.R1302Claim40201.mixedC7C4Row
                                      Tx C ∧
                                    MathlibPlus.Open.ResearchFormalization.R1302Claim40201.fixesEveryCoarseBlock
                                      P C ∧
                                    MathlibPlus.Open.ResearchFormalization.R1302Claim40201.fixesEveryCoarseBlock
                                      (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.conjugateSubgroup
                                        (x : Equiv.Perm Ω) Q) C ∧
                                    ∃ K : Subgroup (Equiv.Perm Ω),
                                      coarseActionKernel Hx C K ∧
                                        P ≤ K ∧
                                          MathlibPlus.Open.ResearchFormalization.R1302Claim40196.conjugateSubgroup
                                              (x : Equiv.Perm Ω) Q ≤ K ∧
                                            ∃ W : Subgroup (Equiv.Perm Ω),
                                              MathlibPlus.Open.ResearchFormalization.R1302Claim40196.sylowSeven
                                                  K W ∧
                                                P ≤ W ∧
                                                  coarseSevenOrbitSqueeze W C ∧
                                                    containsSevenPointOrbit P W ∧
                                                      ∃ k : K,
                                                        let Qx :=
                                                          MathlibPlus.Open.ResearchFormalization.R1302Claim40196.conjugateSubgroup
                                                            (x : Equiv.Perm Ω) Q
                                                        let Qxk :=
                                                          MathlibPlus.Open.ResearchFormalization.R1302Claim40196.conjugateSubgroup
                                                            (k : Equiv.Perm Ω) Qx
                                                        Qxk ≤ W ∧
                                                          coarseSevenOrbitSqueeze Qxk C ∧
                                                            commonTwelveSevenOrbitPartition
                                                              P W Qxk

end MathlibPlus.Open.ResearchFormalization.R1302Claim40199
