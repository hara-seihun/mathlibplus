import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch3412

/-- The prescribed `F₇` order and its prefix vertices. -/
def f7B : Fin 3 → ZMod 7 := ![1, 2, 3]

def f7Prefix : Fin 4 → ZMod 7
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => f7B 0
  | ⟨2, _⟩ => f7B 0 + f7B 1
  | ⟨3, _⟩ => f7B 0 + f7B 1 + f7B 2

def f7InsertionLeft (k : Fin 4) : Finset (ZMod 7) :=
  (Finset.Icc (0 : Fin 4) k).image f7Prefix

def f7InsertionRight (k : Fin 4) : Finset (ZMod 7) :=
  (Finset.Icc k (3 : Fin 4)).image (fun i => f7Prefix i + 4)

/--
The four cuts for inserting `4` into `(1,2,3)` all have an intersection
between the old-prefix side and the shifted-suffix side.
-/
def F7StrongInsertionObstruction : Prop :=
  f7Prefix = ![0, 1, 3, 6] ∧
    Finset.card (Finset.univ.image f7Prefix) = 4 ∧
    f7InsertionLeft 0 ∩ f7InsertionRight 0 = ({0} : Finset (ZMod 7)) ∧
    f7InsertionLeft 1 ∩ f7InsertionRight 1 = ({0} : Finset (ZMod 7)) ∧
    f7InsertionLeft 2 ∩ f7InsertionRight 2 = ({0, 3} : Finset (ZMod 7)) ∧
    f7InsertionLeft 3 ∩ f7InsertionRight 3 = ({3} : Finset (ZMod 7)) ∧
    ∀ k : Fin 4, (f7InsertionLeft k ∩ f7InsertionRight k).Nonempty

/-- The prescribed `F₁₁` order and its prefix vertices. -/
def f11B : Fin 6 → ZMod 11 := ![1, 2, 10, 4, 9, 3]

def f11Prefix : Fin 7 → ZMod 11
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => f11B 0
  | ⟨2, _⟩ => f11B 0 + f11B 1
  | ⟨3, _⟩ => f11B 0 + f11B 1 + f11B 2
  | ⟨4, _⟩ => f11B 0 + f11B 1 + f11B 2 + f11B 3
  | ⟨5, _⟩ => f11B 0 + f11B 1 + f11B 2 + f11B 3 + f11B 4
  | ⟨6, _⟩ => f11B 0 + f11B 1 + f11B 2 + f11B 3 + f11B 4 + f11B 5

def f11RotationAtOne : Fin 7 → ZMod 11 :=
  ![f11Prefix 2 - f11Prefix 1, f11Prefix 3 - f11Prefix 1,
    f11Prefix 4 - f11Prefix 1, f11Prefix 5 - f11Prefix 1,
    f11Prefix 6 - f11Prefix 1, 0, f11Prefix 1]

def f11RotationAtThree : Fin 7 → ZMod 11 :=
  ![f11Prefix 4 - f11Prefix 3, f11Prefix 5 - f11Prefix 3,
    f11Prefix 6 - f11Prefix 3, 0, f11Prefix 1, f11Prefix 2,
    f11Prefix 3]

def f11RotationAtTwo : Fin 7 → ZMod 11 :=
  ![f11Prefix 3 - f11Prefix 2, f11Prefix 4 - f11Prefix 2,
    f11Prefix 5 - f11Prefix 2, f11Prefix 6 - f11Prefix 2,
    0, f11Prefix 1, f11Prefix 2]

def f11RotationAtFive : Fin 7 → ZMod 11 :=
  ![f11Prefix 6 - f11Prefix 5, 0, f11Prefix 1, f11Prefix 2,
    f11Prefix 3, f11Prefix 4, f11Prefix 5]

/--
For `u=5,6,7,8`, the stated endpoint blocks and their forced rotations
have the displayed repeated prefix vertices, so none of the rotations is
strong.
-/
def F11EndpointRotationObstruction : Prop :=
  f11Prefix = ![0, 1, 3, 2, 6, 4, 7] ∧
    (∀ u ∈ ({5, 6, 7, 8} : Finset (ZMod 11)),
      u ∉ Finset.univ.image f11B) ∧
    f11Prefix 6 + 5 = f11Prefix 1 ∧
    f11Prefix 6 + 6 = f11Prefix 3 ∧
    f11Prefix 6 + 7 = f11Prefix 2 ∧
    f11Prefix 6 + 8 = f11Prefix 5 ∧
    Finset.card (Finset.univ.image f11RotationAtOne) < 7 ∧
    Finset.card (Finset.univ.image f11RotationAtThree) < 7 ∧
    Finset.card (Finset.univ.image f11RotationAtTwo) < 7 ∧
    Finset.card (Finset.univ.image f11RotationAtFive) < 7

end MathlibPlus.Open.Research.FormalizationBatch3412
