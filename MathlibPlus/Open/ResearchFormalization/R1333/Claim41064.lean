import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1333.Claim41064

abbrev Omega := ZMod 35

def standardCycle : Equiv.Perm Omega :=
  Equiv.addRight 1

def transposition : Equiv.Perm Omega :=
  Equiv.swap 0 1

def conjugateCycle : Equiv.Perm Omega :=
  transposition⁻¹ * standardCycle * transposition

def generatedGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure ({standardCycle, conjugateCycle} : Set (Equiv.Perm Omega))

def commutator : Equiv.Perm Omega :=
  standardCycle⁻¹ * conjugateCycle⁻¹ * standardCycle * conjugateCycle

/-- The concrete break-both transposition chart generates `A₃₅`, and its
commutator has order three and moves exactly three points. -/
def claim41064 : Prop :=
  generatedGroup = alternatingGroup Omega ∧
    orderOf commutator = 3 ∧
      (Equiv.Perm.support commutator).card = 3

end MathlibPlus.Open.ResearchFormalization.R1333.Claim41064
