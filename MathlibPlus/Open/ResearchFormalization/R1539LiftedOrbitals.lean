import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1539LiftedOrbitals

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

def liftedInversion (p : Omega300) : Omega300 :=
  (p.1⁻¹, (p.2.1⁻¹, p.2.2⁻¹))

def pairOrbit (S : Subgroup (Equiv.Perm Omega300)) (P : Set Omega300) :
    Set (Set Omega300) :=
  {Q | Q.ncard = 2 ∧ ∃ g : S, g.1 '' P = Q}

def isPairOrbital (S : Subgroup (Equiv.Perm Omega300))
    (O : Set (Set Omega300)) : Prop :=
  ∃ P : Set Omega300, P.ncard = 2 ∧ O = pairOrbit S P

def isPairOrbitPartition (S : Subgroup (Equiv.Perm Omega300))
    (O : Fin 50 → Set (Set Omega300)) : Prop :=
  (∀ i, isPairOrbital S (O i)) ∧
    (∀ i j, i ≠ j → O i ≠ O j) ∧
    (∀ P : Set Omega300, P.ncard = 2 → ∃! i, P ∈ O i)

def sizeProfile50 : Fin 50 → ℕ := fun i =>
  if i.1 < 12 then 300
  else if i.1 = 12 then 450
  else if i.1 < 25 then 900 else 1200

/-- Claim 37760: the explicit inversion conjugates the lifted copies and
fixes each of the fifty unordered generated orbitals with the stated size
profile. -/
def claim37760_liftedInversionAndFiftyOrbitals : Prop :=
  (∃ ι : Equiv.Perm Omega300,
    (∀ p : Omega300, ι p = liftedInversion p) ∧
      (∀ p : Equiv.Perm Omega300,
        p ∈ liftedLeftGroup ↔
          ι * p * ι⁻¹ ∈ liftedRightGroup)) ∧
    (∃ O : Fin 50 → Set (Set Omega300),
      isPairOrbitPartition liftedGeneratedGroup O ∧
      (∀ i, (O i).ncard = sizeProfile50 i) ∧
      (∀ i, ∀ P : Set Omega300,
        P ∈ O i ↔ Set.image liftedInversion P ∈ O i))

end

end MathlibPlus.Open.ResearchFormalization.R1539LiftedOrbitals
