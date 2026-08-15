import Mathlib

open scoped Classical

noncomputable section
namespace MathlibPlus.Open.Research.FormalizationBatch

/-- The deletion shadow of a finite family at coordinate y. -/
def collisionShadow20524 {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) (y : α) : Finset (Finset α) :=
  F.filter (fun A => A ⊆ X.erase y ∧ A ∪ {y} ∈ F)

def familyOn20524 {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A ⊆ X

def collisionPair20524 {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) (y : α)
    (A : Finset α) : Prop :=
  A ⊆ X.erase y ∧ A ∈ F ∧ A ∪ {y} ∈ F

/-- Collision-shadow members index exactly the distinct pairs lost by deleting y. -/
def claim20524 {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) (y : α) : Prop :=
  familyOn20524 X F ∧ y ∈ X →
    (∀ A : Finset α,
      A ∈ collisionShadow20524 X F y ↔ collisionPair20524 X F y A) ∧
    (∀ A : Finset α, A ∈ collisionShadow20524 X F y →
      A ∈ F ∧ A ∪ {y} ∈ F ∧ A ≠ A ∪ {y} ∧
        (A.erase y) = (A ∪ {y}).erase y) ∧
    (∀ B C : Finset α,
      B ∈ F → C ∈ F → B ≠ C → B.erase y = C.erase y →
        ∃ A : Finset α,
          A ∈ collisionShadow20524 X F y ∧
            ((B = A ∧ C = A ∪ {y}) ∨
              (C = A ∧ B = A ∪ {y})))

end MathlibPlus.Open.Research.FormalizationBatch
