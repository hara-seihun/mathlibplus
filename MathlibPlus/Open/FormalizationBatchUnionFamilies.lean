import Mathlib

namespace MathlibPlus.Open.FormalizationBatchUnionFamilies

open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]

def familyUnion (F : Finset (Finset α)) : Finset α := by
  classical
  exact F.biUnion id

def unionClosedFamily (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def separatingFamily (F : Finset (Finset α)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y →
    ∃ A ∈ F, (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)

def excludesEmptySet (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.Nonempty

def emptyTotalIntersection (F : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ A ∈ F, x ∉ A

def totallyOrderedByInclusion (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ⊆ B ∨ B ⊆ A

/-- A separating union-closed private-ground family has at most r-1 coordinates. -/
def separatingUnionClosedPrivateGroundBoundClaim20408 : Prop :=
  ∀ (Y : Type*) [Fintype Y] [DecidableEq Y]
    (P : Finset (Finset Y)) (r : ℕ),
    (∅ : Finset Y) ∈ P →
    unionClosedFamily P →
    separatingFamily P →
    P.card = r →
    Fintype.card Y ≤ r - 1

/-- The extremal coordinate-adjacent family is a chain. -/
def extremalSeparatingUnionClosedChainsClaim20495 : Prop :=
  ∀ (Y : Type*) [Fintype Y] [DecidableEq Y]
    (P : Finset (Finset Y)),
    separatingFamily P →
    unionClosedFamily P →
    (∅ : Finset Y) ∈ P →
    P.card = Fintype.card Y + 1 →
    (∀ y : Y, ∃ p : Finset Y, p ∈ P ∧ y ∉ p ∧ p ∪ {y} ∈ P) →
    totallyOrderedByInclusion P

/-- The union product of two finite families of ordinary finite sets. -/
def setUnionProductClaim21271 (A B : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact A.biUnion (fun a => B.image (fun b => a ∪ b))

def noBottomElement (F : Finset (Finset α)) : Prop :=
  ¬∃ c : Finset α, c ∈ F ∧ ∀ d : Finset α, d ∈ F → c ⊆ d

/-- A seven-element union product forces one factor to have size at most eighteen. -/
def sharpSevenOutputFactorCapClaim21272 : Prop :=
  ∀ (A B : Finset (Finset α)),
    A.Nonempty → B.Nonempty →
    unionClosedFamily A → unionClosedFamily B →
    excludesEmptySet A → excludesEmptySet B →
    emptyTotalIntersection A → emptyTotalIntersection B →
    (setUnionProductClaim21271 A B).card = 7 →
    min A.card B.card ≤ 18

/-- Under the normalized hypotheses the union product has no bottom member. -/
def normalizedProductNoBottomClaim21274 : Prop :=
  ∀ (A B : Finset (Finset α)),
    A.Nonempty → B.Nonempty →
    unionClosedFamily A → unionClosedFamily B →
    excludesEmptySet A → excludesEmptySet B →
    emptyTotalIntersection A → emptyTotalIntersection B →
    noBottomElement (setUnionProductClaim21271 A B)

abbrev CounterexampleGround := Fin 31

def counterexampleM₁ : Finset CounterexampleGround := {0}
def counterexampleM₂ : Finset CounterexampleGround := Finset.Icc 1 10
def counterexampleM₃ : Finset CounterexampleGround := Finset.Icc 11 20
def counterexampleD₂ : Finset CounterexampleGround := Finset.Icc 1 3
def counterexampleD₃ : Finset CounterexampleGround := Finset.Icc 11 13
def counterexampleZ : Finset CounterexampleGround := {30}

def counterexampleL₂ : Finset (Finset CounterexampleGround) :=
  counterexampleD₂.powerset ∪ {counterexampleM₂}
def counterexampleL₃ : Finset (Finset CounterexampleGround) :=
  counterexampleD₃.powerset ∪ {counterexampleM₃}
def counterexampleBlocks : Finset (Finset CounterexampleGround) :=
  {counterexampleM₁, counterexampleM₂, counterexampleM₃}
def counterexampleCube : Finset (Finset CounterexampleGround) := by
  classical
  exact counterexampleBlocks.powerset.image (fun C => C.biUnion id)
def counterexampleAdded : Finset (Finset CounterexampleGround) := by
  classical
  exact counterexampleL₂.biUnion (fun P =>
    counterexampleL₃.image (fun Q => counterexampleZ ∪ counterexampleM₁ ∪ P ∪ Q))
def exactOneTenTenFamily : Finset (Finset CounterexampleGround) :=
  counterexampleCube ∪ counterexampleAdded

def minimalNonemptyMember (F : Finset (Finset α)) (S : Finset α) : Prop :=
  S ∈ F ∧ S.Nonempty ∧
    ∀ T : Finset α, T ∈ F → T.Nonempty → T ⊆ S → T = S

/-- The explicit 1+10+10 normalized-charge family has 89 members and the three stated minima. -/
def exactOneTenTenCounterexampleClaim22954 : Prop :=
  counterexampleM₁.card = 1 ∧
  counterexampleM₂.card = 10 ∧
  counterexampleM₃.card = 10 ∧
  Disjoint counterexampleM₁ counterexampleM₂ ∧
  Disjoint counterexampleM₁ counterexampleM₃ ∧
  Disjoint counterexampleM₂ counterexampleM₃ ∧
  counterexampleD₂ ⊆ counterexampleM₂ ∧ counterexampleD₂.card = 3 ∧
  counterexampleD₃ ⊆ counterexampleM₃ ∧ counterexampleD₃.card = 3 ∧
  Disjoint counterexampleZ
    (counterexampleM₁ ∪ counterexampleM₂ ∪ counterexampleM₃) ∧
  exactOneTenTenFamily.card = 89 ∧
  unionClosedFamily exactOneTenTenFamily ∧
  (∀ S : Finset CounterexampleGround,
    minimalNonemptyMember exactOneTenTenFamily S ↔
      S = counterexampleM₁ ∨ S = counterexampleM₂ ∨ S = counterexampleM₃)

end

end MathlibPlus.Open.FormalizationBatchUnionFamilies
