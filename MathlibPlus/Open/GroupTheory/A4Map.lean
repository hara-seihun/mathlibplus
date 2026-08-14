import Mathlib

namespace MathlibPlus.Open.GroupTheory.A4Map

private def v4Add (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 0 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 0 => 3
  | 3, 1 => 2
  | 3, 2 => 1
  | 3, 3 => 0
  | _, _ => 0

private def v4Action (c : Fin 3) (v : Fin 4) : Fin 4 :=
  match c.val, v.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 0
  | 1, 1 => 2
  | 1, 2 => 3
  | 1, 3 => 1
  | 2, 0 => 0
  | 2, 1 => 3
  | 2, 2 => 1
  | 2, 3 => 2
  | _, _ => 0

private def a4Encode (v : Fin 4) (c : Fin 3) : Fin 12 :=
  ⟨3 * v.val + c.val, by omega⟩

private def a4V (x : Fin 12) : Fin 4 :=
  ⟨x.val / 3, by omega⟩

private def a4C (x : Fin 12) : Fin 3 :=
  ⟨x.val % 3, Nat.mod_lt _ (by norm_num)⟩

private def c3Add (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by norm_num)⟩

private def a4Mul (x y : Fin 12) : Fin 12 :=
  a4Encode (v4Add (a4V x) (v4Action (a4C x) (a4V y))) (c3Add (a4C x) (a4C y))

private def q : Fin 12 → Fin 12
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 4
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 7
  | ⟨8, _⟩ => 11
  | ⟨9, _⟩ => 2
  | ⟨10, _⟩ => 5
  | ⟨11, _⟩ => 8

private def α : Fin 12 → Fin 12
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 9
  | ⟨7, _⟩ => 10
  | ⟨8, _⟩ => 11
  | ⟨9, _⟩ => 6
  | ⟨10, _⟩ => 7
  | ⟨11, _⟩ => 8

private def a4Automorphism (f : Fin 12 → Fin 12) : Prop :=
  Function.Bijective f ∧ ∀ x y, f (a4Mul x y) = a4Mul (f x) (f y)

/-- The fixed twelve-element coordinate map and the retained automorphism are
recorded against the explicit `A₄ ≅ V₄ ⋊ C₃` multiplication table. -/
def claim29086 : Prop :=
  (∀ i : Fin 12, q i =
    match i.val with
    | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 3 | 4 => 4 | 5 => 10
    | 6 => 6 | 7 => 7 | 8 => 11 | 9 => 2 | 10 => 5 | 11 => 8 | _ => 0) ∧
    (∀ i : Fin 12, α i =
    match i.val with
    | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
    | 6 => 9 | 7 => 10 | 8 => 11 | 9 => 6 | 10 => 7 | 11 => 8 | _ => 0) ∧
    Function.Bijective q ∧
    ¬ (∀ x y : Fin 12, q (a4Mul x y) = a4Mul (q x) (q y)) ∧
    a4Automorphism α

end MathlibPlus.Open.GroupTheory.A4Map
