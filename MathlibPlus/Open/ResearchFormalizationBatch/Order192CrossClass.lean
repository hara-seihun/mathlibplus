import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Order192CrossClass

abbrev degreeEightPoint := Fin 8
abbrev transposition (i j : degreeEightPoint) : Equiv.Perm degreeEightPoint := Equiv.swap i j

def cycleA : Equiv.Perm degreeEightPoint :=
  transposition 0 1 * transposition 1 2 * transposition 2 3 *
    transposition 3 4 * transposition 4 5 * transposition 5 6 * transposition 6 7

def cycleB : Equiv.Perm degreeEightPoint :=
  transposition 0 1 * transposition 1 3 * transposition 3 2 *
    transposition 2 4 * transposition 4 5 * transposition 5 7 * transposition 7 6

def order192Ambient : Subgroup (Equiv.Perm degreeEightPoint) :=
  Subgroup.closure ({cycleA, cycleB} : Set (Equiv.Perm degreeEightPoint))

def regularCyclicEight (H : Subgroup (Equiv.Perm degreeEightPoint)) : Prop :=
  Nat.card H = 8 ∧
    Function.Bijective (fun g : H => (g : Equiv.Perm degreeEightPoint) 0)

def conjugateWithinOrder192
    (H K : Subgroup (Equiv.Perm degreeEightPoint)) : Prop :=
  ∃ g : order192Ambient,
    Subgroup.map
      (MulEquiv.toMonoidHom (MulAut.conj (g : Equiv.Perm degreeEightPoint))) H = K

def explicitOrder192CrossClass : Prop :=
  regularCyclicEight (Subgroup.zpowers cycleA) ∧
  regularCyclicEight (Subgroup.zpowers cycleB) ∧
  Subgroup.zpowers cycleA ≤ order192Ambient ∧
  Subgroup.zpowers cycleB ≤ order192Ambient ∧
  ¬ conjugateWithinOrder192
      (Subgroup.zpowers cycleA) (Subgroup.zpowers cycleB) ∧
  Nat.card order192Ambient = 192

def explicitOrder192CrossClassDuplicate : Prop :=
  regularCyclicEight (Subgroup.zpowers cycleA) ∧
  regularCyclicEight (Subgroup.zpowers cycleB) ∧
  Subgroup.zpowers cycleA ≤ order192Ambient ∧
  Subgroup.zpowers cycleB ≤ order192Ambient ∧
  ¬ conjugateWithinOrder192
      (Subgroup.zpowers cycleA) (Subgroup.zpowers cycleB) ∧
  Nat.card order192Ambient = 192

end MathlibPlus.Open.ResearchFormalizationBatch.Order192CrossClass
