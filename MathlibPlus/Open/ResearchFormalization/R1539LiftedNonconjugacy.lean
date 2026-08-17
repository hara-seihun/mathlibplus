import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1539LiftedNonconjugacy

noncomputable section

abbrev C5 := Multiplicative (ZMod 5)
abbrev A4 := alternatingGroup (Fin 4)
abbrev Omega := C5 × A4
abbrev Omega300 := C5 × Omega

def baseLeftAction (t : C5) (g : A4) (p : Omega) : Omega :=
  (t * p.1, g * p.2)

def baseRightAction (t : C5) (g : A4) (p : Omega) : Omega :=
  (t * p.1, p.2 * g)

def baseLeftSet : Set (Equiv.Perm Omega) :=
  {e | ∃ t : C5, ∃ g : A4, ∀ p, e p = baseLeftAction t g p}

def baseRightSet : Set (Equiv.Perm Omega) :=
  {e | ∃ t : C5, ∃ g : A4, ∀ p, e p = baseRightAction t g p}

def baseLeftGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure baseLeftSet

def baseRightGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure baseRightSet

def baseGeneratedGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (baseLeftSet ∪ baseRightSet)

def liftedLeftAction (d t : C5) (g : A4) (p : Omega300) : Omega300 :=
  (d * p.1, (t * p.2.1, g * p.2.2))

def liftedRightAction (d t : C5) (g : A4) (p : Omega300) : Omega300 :=
  (d * p.1, (t * p.2.1, p.2.2 * g))

def liftedLeftSet : Set (Equiv.Perm Omega300) :=
  {e | ∃ d t : C5, ∃ g : A4,
    ∀ p, e p = liftedLeftAction d t g p}

def liftedRightSet : Set (Equiv.Perm Omega300) :=
  {e | ∃ d t : C5, ∃ g : A4,
    ∀ p, e p = liftedRightAction d t g p}

def liftedLeftGroup : Subgroup (Equiv.Perm Omega300) :=
  Subgroup.closure liftedLeftSet

def liftedRightGroup : Subgroup (Equiv.Perm Omega300) :=
  Subgroup.closure liftedRightSet

def productLiftedSet : Set (Equiv.Perm Omega300) :=
  {e | ∃ d : C5, ∃ x : baseGeneratedGroup,
    ∀ p, e p = (d * p.1, x.1 p.2)}

def liftedGeneratedGroup : Subgroup (Equiv.Perm Omega300) :=
  Subgroup.closure productLiftedSet

def normalIn
    (S T : Subgroup (Equiv.Perm Omega300)) : Prop :=
  S ≤ T ∧ ∀ t : T, ∀ s : S,
    t.1 * s.1 * (t.1)⁻¹ ∈ S

/-- Claim 37758: the lifted left and right copies are distinct normal
subgroups of the generated order-3600 group and are not conjugate inside it. -/
def claim37758_liftedPairInternallyNonconjugate : Prop :=
  liftedLeftGroup ≠ liftedRightGroup ∧
    normalIn liftedLeftGroup liftedGeneratedGroup ∧
    normalIn liftedRightGroup liftedGeneratedGroup ∧
    Nat.card liftedGeneratedGroup = 3600 ∧
    (liftedGeneratedGroup =
      Subgroup.closure
        ((liftedLeftSet : Set (Equiv.Perm Omega300)) ∪
          (liftedRightSet : Set (Equiv.Perm Omega300)))) ∧
    (liftedLeftSet = (liftedLeftGroup : Set (Equiv.Perm Omega300))) ∧
    (liftedRightSet = (liftedRightGroup : Set (Equiv.Perm Omega300))) ∧
    ¬ ∃ x : liftedGeneratedGroup, ∀ p : Equiv.Perm Omega300,
      p ∈ liftedLeftGroup ↔
        x.1 * p * (x.1)⁻¹ ∈ liftedRightGroup

end

end MathlibPlus.Open.ResearchFormalization.R1539LiftedNonconjugacy
