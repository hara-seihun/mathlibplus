import MathlibPlus.Open.ResearchFormalization.R1302Claim40201

namespace MathlibPlus.Open.ResearchFormalization.R1302Claim40194

open MathlibPlus.Open.ResearchFormalization.R1302Claim40197
open MathlibPlus.Open.ResearchFormalization.R1302Claim40201

/-- The hypotheses describing the pure `C₄` setup, without its asserted
stabilizer, kernel, or induced-action conclusions. -/
def pureC4Hypotheses {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (R T X : Subgroup (Equiv.Perm Ω)) : Prop :=
  fourBlockSystem B ∧
    regularG84 R ∧
      regularG84 T ∧
        X = generatedPair R T ∧
          preservesBlockSystem X B

/-- The conclusions attached to an arbitrary pure `C₄` setup.  The two
regular copies have their exact block stabilizers and block kernels, the
central `C₂` intersections, and their induced nonregular `C₇ × S₃` rows. -/
structure PureC4ConclusionData {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (R T : Subgroup (Equiv.Perm Ω)) where
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

/-- The pure `C₄` conclusions are asserted for the given copies and block
system, rather than bundled into the setup hypotheses. -/
def pureC4Conclusions {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (PureC4ConclusionData B R T)

/-- Claim 40194: the concrete group has order 84 and the displayed
quaternion presentation; every arbitrary regular pair on an 84-point set
with a common invariant pure-`C₄` block system has the stated stabilizer,
central-kernel, and induced-action structure. -/
def claim40194 : Prop :=
  Fintype.card Q12 = 12 ∧
    Fintype.card G84 = 84 ∧
      displayedQ12Presentation ∧
        ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
          Fintype.card Ω = 84 →
            ∀ (B : Finset (Set Ω))
              (R T X : Subgroup (Equiv.Perm Ω)),
              pureC4Hypotheses B R T X →
                pureC4Conclusions B R T

end MathlibPlus.Open.ResearchFormalization.R1302Claim40194
