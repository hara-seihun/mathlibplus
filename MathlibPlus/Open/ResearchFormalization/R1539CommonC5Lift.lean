import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1539CommonC5Lift

noncomputable section

abbrev C5 := Multiplicative (ZMod 5)
abbrev A4 := alternatingGroup (Fin 4)
abbrev Omega := C5 × A4
abbrev Omega300 := C5 × Omega

/-- The left and right regular action formulas on `C₅ × A₄`. -/
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

def dAction (d : C5) (p : Omega300) : Omega300 :=
  (d * p.1, p.2)

def dSet : Set (Equiv.Perm Omega300) :=
  {e | ∃ d : C5, ∀ p, e p = dAction d p}

def dGroup : Subgroup (Equiv.Perm Omega300) :=
  Subgroup.closure dSet

def productLiftedSet : Set (Equiv.Perm Omega300) :=
  {e | ∃ d : C5, ∃ x : baseGeneratedGroup,
    ∀ p, e p = (d * p.1, x.1 p.2)}

def liftedGeneratedGroup : Subgroup (Equiv.Perm Omega300) :=
  Subgroup.closure productLiftedSet

def regularSet {P : Type*} (S : Set (Equiv.Perm P)) : Prop :=
  ∀ x y : P, ∃! e : Equiv.Perm P, e ∈ S ∧ e x = y

def dOrbit (p : Omega300) : Set Omega300 :=
  {q | ∃ d : C5, dAction d p = q}

def inducedPair (S : Subgroup (Equiv.Perm Omega300))
    (Q : Set (Equiv.Perm Omega)) : Prop :=
  (∀ s : S, ∃ q : Q, ∀ p : Omega300,
    (s.1 p).2 = q.1 p.2) ∧
  (∀ q : Q, ∃ s : S, ∀ p : Omega300,
    (s.1 p).2 = q.1 p.2)

/-- Claim 37757: the common-C5 lift has the stated regular copies, orders,
intersection, generated order, sixty common five-point blocks, and base
quotient pair.  No regularity of the block action of `D` on all 300 points
is asserted. -/
def claim37757_commonC5Lift : Prop :=
  (liftedLeftSet = (liftedLeftGroup : Set (Equiv.Perm Omega300))) ∧
    (liftedRightSet = (liftedRightGroup : Set (Equiv.Perm Omega300))) ∧
    regularSet liftedLeftSet ∧
    regularSet liftedRightSet ∧
    Nonempty ((C5 × (C5 × A4)) ≃* liftedLeftGroup) ∧
    Nonempty ((C5 × (C5 × A4)) ≃* liftedRightGroup) ∧
    Nat.card liftedLeftGroup = 300 ∧
    Nat.card liftedRightGroup = 300 ∧
    Nat.card (↥(liftedLeftGroup ⊓ liftedRightGroup)) = 25 ∧
    (liftedGeneratedGroup =
      Subgroup.closure
        ((liftedLeftSet : Set (Equiv.Perm Omega300)) ∪
          (liftedRightSet : Set (Equiv.Perm Omega300)))) ∧
    Nat.card liftedGeneratedGroup = 3600 ∧
    (dSet = (dGroup : Set (Equiv.Perm Omega300))) ∧
    Nonempty (C5 ≃* dGroup) ∧
    dGroup ≤ liftedLeftGroup ⊓ liftedRightGroup ∧
    (∀ p : Omega300, (dOrbit p).ncard = 5) ∧
    Set.ncard {s : Set Omega300 | ∃ p : Omega300, s = dOrbit p} = 60 ∧
    inducedPair liftedLeftGroup baseLeftSet ∧
    inducedPair liftedRightGroup baseRightSet

end

end MathlibPlus.Open.ResearchFormalization.R1539CommonC5Lift
