import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
import MathlibPlus.Open.NewResearch2.R0390Claim20811

namespace MathlibPlus.Open.ResearchFormalization.R0390Claim20809

noncomputable section

open MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
open MathlibPlus.Open.NewResearch2.R0390Claim20811

/-- The normalized complementary family is the concrete 61-member family on
its eight-bit ground, with the atomistic singleton-coordinate core and all of
the reviewed tight-fiber and removable-kernel properties. -/
def complementaryUnionClosedFamilyNormalization_claim20809 : Prop :=
  claim20802 ∧
  familyNormalization ∧
  singletonFiberFactorization ∧
  baseAbsorption ∧
  emptyIntersectionInNonemptyTightFibers ∧
  removableSingletonTraceKernels

end

end MathlibPlus.Open.ResearchFormalization.R0390Claim20809
