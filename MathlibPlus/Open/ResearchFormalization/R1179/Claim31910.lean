import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim31910

noncomputable section

abbrev C3Squared := Multiplicative (Fin 2 → ZMod 3)
abbrev D10 := DihedralGroup 5
abbrev G := C3Squared × D10

def isConnectionSet (S : Set G) : Prop :=
  (1 : G) ∉ S ∧
    ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

def leftStep (S : Set G) (x y : G) : Prop :=
  ∃ g ∈ S, g * x = y

def cayleyGraph (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (leftStep S)

def graphAutomorphism (Γ : SimpleGraph G) (e : Equiv.Perm G) : Prop :=
  ∀ x y, Γ.Adj x y ↔ Γ.Adj (e x) (e y)

def fullGraphAutomorphismSubgroup (Γ : SimpleGraph G)
    (Aut : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ e : Equiv.Perm G, e ∈ Aut ↔ graphAutomorphism Γ e

def naturalC5Orbit (x : G) : Set G :=
  {y | ∃ k : ZMod 5,
    y = x * ((1 : C3Squared), DihedralGroup.r k)}

def preservesNaturalC5Partition (S : Set G) : Prop :=
  ∀ e : Equiv.Perm G,
    graphAutomorphism (cayleyGraph S) e →
      ∀ x y : G,
        y ∈ naturalC5Orbit x ↔
          e y ∈ naturalC5Orbit (e x)

/-- The diagonal left-regular copy of `C₃²` in the vertex permutation group. -/
def diagonalAction : C3Squared →* Equiv.Perm G :=
  (MulAction.toPermHom G G).comp
    (MonoidHom.inl C3Squared D10)

def diagonalHall : Subgroup (Equiv.Perm G) :=
  diagonalAction.range

def diagonalHallContained
    (Aut : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ h : Equiv.Perm G, h ∈ diagonalHall → h ∈ Aut

/-- Exact membership in the centralizer of the diagonal copy inside the full
graph automorphism group. -/
def diagonalCentralizerCarrier
    (Aut C : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ e : Equiv.Perm G,
    e ∈ C ↔
      e ∈ Aut ∧
        ∀ h : Equiv.Perm G,
          h ∈ diagonalHall → e * h = h * e

def normalThreeCore {C : Type*} [Group C]
    (N : Subgroup C) : Prop :=
  N.Normal ∧
    IsPGroup 3 N ∧
      ∀ M : Subgroup C,
        M.Normal → IsPGroup 3 M → M ≤ N

def complementTo {C : Type*} [Group C]
    (N H : Subgroup C) : Prop :=
  Subgroup.IsComplement (N : Set C) (H : Set C)

def conjugateSubgroups {C : Type*} [Group C]
    (H K : Subgroup C) : Prop :=
  ∃ c : C, ∀ x : C,
    x ∈ H ↔ c * x * c⁻¹ ∈ K

/-- A regular target considered inside the full graph automorphism carrier. -/
def regularTargetAut
    (Aut : Subgroup (Equiv.Perm G))
    (T : Subgroup Aut) : Prop :=
  Nonempty (T ≃* (C3Squared × D10)) ∧
    ∀ x y : G, ∃! t : T,
      ((t : Aut) : Equiv.Perm G) x = y

/-- A regular target considered inside the diagonal centralizer. -/
def regularTargetCentralizer
    (C : Subgroup (Equiv.Perm G))
    (T : Subgroup C) : Prop :=
  Nonempty (T ≃* (C3Squared × D10)) ∧
    ∀ x y : G, ∃! t : T,
      ((t : C) : Equiv.Perm G) x = y

/-- The displayed thick/thin connection set. -/
def thickThinConnection : Set G :=
  ((Set.univ : Set C3Squared) ×ˢ
      ({DihedralGroup.sr 0} : Set D10)) ∪
    {((1 : C3Squared), DihedralGroup.r 1 * DihedralGroup.sr 0)}

/-- Claim 31910: the diagonal centralizer has the exact normal-3-core and
complement data, while both its regular targets and all regular targets in the
full graph automorphism carrier form one nonempty class. -/
def claim31910 : Prop :=
  isConnectionSet thickThinConnection ∧
    Set.ncard thickThinConnection = 10 ∧
    SimpleGraph.Connected (cayleyGraph thickThinConnection) ∧
    ¬ preservesNaturalC5Partition thickThinConnection ∧
    ∃ Aut : Subgroup (Equiv.Perm G),
      fullGraphAutomorphismSubgroup
          (cayleyGraph thickThinConnection) Aut ∧
      diagonalHallContained Aut ∧
      (∀ P : Sylow 5 Aut, Nat.card P = 15625) ∧
      (∀ M : Subgroup Aut,
        M.Normal → IsPGroup 5 M → M = ⊥) ∧
      (∃ T : Subgroup Aut, regularTargetAut Aut T) ∧
      (∀ T U : Subgroup Aut,
        regularTargetAut Aut T →
          regularTargetAut Aut U →
            conjugateSubgroups T U) ∧
      ∃ C : Subgroup (Equiv.Perm G),
        diagonalCentralizerCarrier Aut C ∧
        Nat.card C = 590490 ∧
        (∃ N : Subgroup C,
          normalThreeCore N ∧
            Nat.card N = 59049 ∧
            Subgroup.index N = 10 ∧
            ∃ H : Subgroup C,
              complementTo N H ∧
                Nonempty (H ≃* D10) ∧
                ∀ K : Subgroup C,
                  complementTo N K → conjugateSubgroups K H) ∧
        (∃ T : Subgroup C,
          regularTargetCentralizer C T) ∧
        (∀ T U : Subgroup C,
          regularTargetCentralizer C T →
            regularTargetCentralizer C U →
              conjugateSubgroups T U)

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim31910
