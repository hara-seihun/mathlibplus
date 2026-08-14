import Mathlib

open scoped Classical
noncomputable section

namespace MathlibPlus.Open.Combinatorics

abbrev FiveSet := Finset (Fin 5)
abbrev FiveFamily := Finset FiveSet

def familyUnionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def removableMember {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) : Prop :=
  M ∈ F ∧
    ∀ ⦃A B : Finset α⦄, A ∈ F → A ≠ M → B ∈ F → B ≠ M →
      A ∪ B ∈ F.erase M

def familyCoreIntersection {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  (Finset.univ : Finset α).filter (fun x => ∀ A ∈ F, x ∈ A)

def fiveMask11 : FiveSet := {0, 1, 3}
def fiveMask13 : FiveSet := {0, 2, 3}
def fiveMask15 : FiveSet := {0, 1, 2, 3}
def fiveMask19 : FiveSet := {0, 1, 4}
def fiveMask21 : FiveSet := {0, 2, 4}
def fiveMask23 : FiveSet := {0, 1, 2, 4}
def fiveMask27 : FiveSet := {0, 1, 3, 4}
def fiveMask29 : FiveSet := {0, 2, 3, 4}
def fiveMask31 : FiveSet := {0, 1, 2, 3, 4}
def fiveMask7 : FiveSet := {0, 1, 2}

def separatorFamilyH : FiveFamily :=
  {fiveMask11, fiveMask13, fiveMask15, fiveMask19, fiveMask21,
    fiveMask23, fiveMask27, fiveMask29, fiveMask31}

/-- Claim 45403: the displayed five-coordinate family is an exact obstruction to the
ordinary separator-demand inference. -/
def exactOrdinarySeparatorDemandObstruction_claim45403 : Prop :=
  let H := separatorFamilyH
  let R := fiveMask7
  let D : FiveSet := {1, 2}
  let extended := insert R H
  familyUnionClosed H ∧
    (∀ A ∈ H, 3 ≤ A.card) ∧
    familyUnionClosed extended ∧
    R ∉ H ∧
    removableMember extended R ∧
    familyCoreIntersection H ∩ R = ({0} : FiveSet) ∧
    (∀ M : FiveSet, removableMember H M ↔
      M = fiveMask11 ∨ M = fiveMask13 ∨ M = fiveMask19 ∨ M = fiveMask21) ∧
    (∀ x : Fin 5,
      (∀ M : FiveSet, removableMember H M → x ∈ M) ↔ x = 0) ∧
    (∀ M : FiveSet, removableMember H M → ¬ D ⊆ M) ∧
    (∀ M : FiveSet, M ∈ H → D ⊆ M →
      M = fiveMask15 ∨ M = fiveMask23 ∨ M = fiveMask31) ∧
    fiveMask15 = fiveMask11 ∪ fiveMask13 ∧
    fiveMask23 = fiveMask19 ∪ fiveMask21 ∧
    fiveMask31 = fiveMask11 ∪ fiveMask21 ∧
    fiveMask31 = fiveMask19 ∪ fiveMask13

end MathlibPlus.Open.Combinatorics
