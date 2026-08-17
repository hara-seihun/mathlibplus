import MathlibPlus.Open.ResearchFormalization.R1302Claim40196
import MathlibPlus.Open.ResearchFormalization.R1302Claim40197

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40201

open MathlibPlus.Open.ResearchFormalization.R1302Claim40197

abbrev C4 := Multiplicative (ZMod 4)
abbrev C2 := Multiplicative (ZMod 2)
abbrev C7S3 := C7 × Equiv.Perm (Fin 3)
abbrev C7C4 := C7 × C4
abbrev C7C2 := C7 × C2

def displayedQ12Presentation : Prop :=
  ∃ a b : Q12,
    a ^ 6 = 1 ∧
      b ^ 2 = a ^ 3 ∧
        b⁻¹ * a * b = a⁻¹ ∧
          Subgroup.closure ({a, b} : Set Q12) = ⊤

def preservesBlockSystem {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (B : Finset (Set Ω)) : Prop :=
  ∀ h : H, ∀ U ∈ B,
    ∃ V ∈ B, (h : Equiv.Perm Ω) '' U = V

def blockStabilizerCorrect {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (U : Set Ω) (S : Subgroup H) : Prop :=
  ∀ h : H, h ∈ S ↔ (h : Equiv.Perm Ω) '' U = U

def blockKernelCorrect {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (B : Finset (Set Ω)) (K : Subgroup H) : Prop :=
  ∀ h : H, h ∈ K ↔
    ∀ U : BlockPoint B, (h : Equiv.Perm Ω) '' U.1 = U.1

def centralC2Intersection {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (B : Finset (Set Ω))
    (stabilizer : BlockPoint B → Subgroup H)
    (kernel : Subgroup H) : Prop :=
  ∀ U : BlockPoint B,
    Nonempty (C2 ≃* ((stabilizer U ⊓ kernel : Subgroup H))) ∧
      ∀ z : (stabilizer U ⊓ kernel : Subgroup H), ∀ h : H,
        (z : H) * h = h * (z : H)

def regularOn {α : Type*}
    (H : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! h : H, (h : Equiv.Perm α) x = y

def pointStabilizer {α : Type*}
    (H : Subgroup (Equiv.Perm α)) (u : α) : Subgroup H :=
  (MulAction.stabilizer (Equiv.Perm α) u).comap H.subtype

def inducedC7S3Row {Ω : Type*}
    (B : Finset (Set Ω))
    (H : Subgroup (Equiv.Perm Ω))
    (ρ : H →* BlockPerm B) : Prop :=
  Nonempty (C7S3 ≃* ρ.range) ∧
    ¬regularOn ρ.range ∧
      ∀ U : BlockPoint B,
        Nonempty (C2 ≃* pointStabilizer ρ.range U)

structure PureC4Data {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (R T X : Subgroup (Equiv.Perm Ω)) where
  blocks : fourBlockSystem B
  R_regular : regularG84 R
  T_regular : regularG84 T
  generated : X = generatedPair R T
  R_in_X : R ≤ X
  T_in_X : T ≤ X
  X_preserves : preservesBlockSystem X B
  rhoR : R →* BlockPerm B
  rhoT : T →* BlockPerm B
  rhoR_action : inducedBlockAction R B rhoR
  rhoT_action : inducedBlockAction T B rhoT
  stabilizerR : BlockPoint B → Subgroup R
  stabilizerT : BlockPoint B → Subgroup T
  stabilizerR_correct : ∀ U : BlockPoint B,
    blockStabilizerCorrect R U.1 (stabilizerR U)
  stabilizerT_correct : ∀ U : BlockPoint B,
    blockStabilizerCorrect T U.1 (stabilizerT U)
  kernelR : Subgroup R
  kernelT : Subgroup T
  kernelR_correct : blockKernelCorrect R B kernelR
  kernelT_correct : blockKernelCorrect T B kernelT
  R_stabilizer_C4 : ∀ U : BlockPoint B,
    Nonempty (C4 ≃* stabilizerR U)
  T_stabilizer_C4 : ∀ U : BlockPoint B,
    Nonempty (C4 ≃* stabilizerT U)
  R_kernel_core_C2 : centralC2Intersection R B stabilizerR kernelR
  T_kernel_core_C2 : centralC2Intersection T B stabilizerT kernelT
  R_induced_row : inducedC7S3Row B R rhoR
  T_induced_row : inducedC7S3Row B T rhoT

def pureC4Row {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (R T X : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (PureC4Data B R T X)

def familyKernelCorrect {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (C : Set (Set Ω)) (K : Subgroup H) : Prop :=
  ∀ h : H, h ∈ K ↔ ∀ D ∈ C,
    (h : Equiv.Perm Ω) '' D = D

def mixedC7C4Row {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (C : Set (Set Ω)) : Prop :=
  ∃ K : Subgroup H,
    familyKernelCorrect H C K ∧
      ∀ D ∈ C, ∃ S : Subgroup H,
        blockStabilizerCorrect H D S ∧
          Nonempty (C7C4 ≃* S) ∧
            Nonempty (C7C2 ≃* (S ⊓ K : Subgroup H))

def preservesBlockFamily {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (C : Set (Set Ω)) : Prop :=
  ∀ h : H, ∀ D ∈ C,
    (h : Equiv.Perm Ω) '' D ∈ C

def fixesEveryCoarseBlock {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω))
    (C : Set (Set Ω)) : Prop :=
  ∀ h : H, ∀ D ∈ C,
    (h : Equiv.Perm Ω) '' D = D

def inCoarseBlockKernel {Ω : Type*}
    {H : Subgroup (Equiv.Perm Ω)}
    (C : Set (Set Ω)) (k : H) : Prop :=
  ∀ D ∈ C, (k : Equiv.Perm Ω) '' D = D

def twelveSevenOrbitPartition {Ω : Type*}
    (P Q : Subgroup (Equiv.Perm Ω)) : Prop :=
  MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P =
      MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition Q ∧
    (MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P).ncard = 12 ∧
      ∀ D ∈ MathlibPlus.Open.ResearchFormalization.R1302Claim40196.orbitPartition P,
        D.ncard = 7

/-- Claim 40201: the pure `C₄` setup has the two allowed conjugation stages,
passes through the mixed `C₇ × C₄` size-28 row, and ends with equality of the
characteristic-`C₇` orbit partitions.  No CI or DCI conclusion is asserted. -/
def claim40201 : Prop :=
  Fintype.card Q12 = 12 ∧
    Fintype.card G84 = 84 ∧
      displayedQ12Presentation ∧
        ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
          Fintype.card Ω = 84 →
            ∀ (B : Finset (Set Ω))
              (R T X : Subgroup (Equiv.Perm Ω)),
              pureC4Row B R T X →
                ∃ P Q : Subgroup (Equiv.Perm Ω),
                  isO7 R P ∧ isO7 T Q ∧
                    ∃ x : X,
                      let Tx :=
                        conjugateSubgroup (x : Equiv.Perm Ω) T
                      let Hx := generatedPair R Tx
                      ∃ C : Set (Set Ω),
                        threeBlockCoarsening B C ∧
                          preservesBlockFamily Hx C ∧
                            mixedC7C4Row R C ∧
                              mixedC7C4Row Tx C ∧
                                fixesEveryCoarseBlock P C ∧
                                  fixesEveryCoarseBlock
                                    (conjugateSubgroup (x : Equiv.Perm Ω) Q) C ∧
                                    ∃ k : Hx,
                                      inCoarseBlockKernel C k ∧
                                        twelveSevenOrbitPartition P
                                          (conjugateSubgroup
                                            ((x : Equiv.Perm Ω) *
                                              (k : Equiv.Perm Ω)) Q)

end MathlibPlus.Open.ResearchFormalization.R1302Claim40201
