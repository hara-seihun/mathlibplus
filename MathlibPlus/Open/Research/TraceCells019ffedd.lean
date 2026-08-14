import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedd

/-- Claim 21760: the tight trace fiber over every outside mask. -/
def outsideMaskTraceCell_21760
    {α : Type*}
    (T Y : Set α)
    (F : Set (Set α))
    (H : Set α → Set (Set α)) : Prop :=
  ∀ B : Set α, B ⊆ Y →
    H B = {S : Set α | S ⊆ T ∧ S ∪ B ∈ F}

/-- Claim 21774: the deficit of a tight coordinate in a finite shape. -/
def shapeDeficitFormula_21774
    {α : Type*} [DecidableEq α]
    (T : Finset α)
    (H : Finset (Finset α))
    (t_i : α)
    (d_i_H : ℤ) : Prop :=
  t_i ∈ T →
    d_i_H =
      (H.card : ℤ) -
        2 * ((H.filter (fun S => t_i ∈ S)).card : ℤ)

/-- Claim 21775: the full tight and outside deficit formulas. -/
def fullDeficitFormulas_21775
    {α : Type*} [DecidableEq α]
    (T Y : Finset α)
    (H : Finset α → Finset (Finset α))
    (DeltaT : α → ℤ)
    (DeltaY : α → ℤ) : Prop :=
  (∀ t_i : α, t_i ∈ T →
    DeltaT t_i =
      ∑ B ∈ Y.powerset,
        (((H B).card : ℤ) -
          2 * (((H B).filter (fun S => t_i ∈ S)).card : ℤ))) ∧
  (∀ y : α, y ∈ Y →
    DeltaY y =
      ∑ B ∈ Y.powerset,
        (((H B).card : ℤ) *
          (1 - 2 * (if y ∈ B then (1 : ℤ) else 0))))

/-- Claim 21777: the adjacent-fiber collision cell. -/
def collisionCell_21777
    {α : Type*} [DecidableEq α]
    (Y : Finset α)
    (y : α)
    (H K : Finset α → Finset (Finset α)) : Prop :=
  y ∈ Y →
    ∀ B ∈ (Y.erase y).powerset,
      K B = H B ∩ H (insert y B)

/-- Claim 21778: reconstruction of the collision shadow from its cells. -/
def collisionShadowReconstruction_21778
    {α : Type*} [DecidableEq α]
    (Y : Finset α)
    (y : α)
    (K : Finset α → Finset (Finset α))
    (collisionShadow : Set (Finset α)) : Prop :=
  y ∈ Y →
    collisionShadow =
      {U : Finset α |
        ∃ B ∈ (Y.erase y).powerset,
          ∃ S ∈ K B, U = S ∪ B}

/-- Claim 21779: the tight and outside collision-deficit formulas. -/
def collisionDeficitFormulas_21779
    {α : Type*} [DecidableEq α]
    (T Y : Finset α)
    (y : α)
    (K : Finset α → Finset (Finset α))
    (deltaT deltaOutside : α → α → ℤ) : Prop :=
  y ∈ Y →
    (∀ t_i : α, t_i ∈ T →
      deltaT y t_i =
        ∑ B ∈ (Y.erase y).powerset,
          (((K B).card : ℤ) -
            2 * (((K B).filter (fun S => t_i ∈ S)).card : ℤ))) ∧
    (∀ x : α, x ∈ Y.erase y →
      deltaOutside y x =
        ∑ B ∈ (Y.erase y).powerset,
          (((K B).card : ℤ) *
            (1 - 2 * (if x ∈ B then (1 : ℤ) else 0))))

end MathlibPlus.Open.Research.FormalizationBatch019ffedd
