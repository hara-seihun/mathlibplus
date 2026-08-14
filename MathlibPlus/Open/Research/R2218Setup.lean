import Mathlib

namespace MathlibPlus.Open.Research

abbrev R2218F7 := ZMod 7
abbrev R2218Vector := Fin 3 → R2218F7
abbrev R2218G := R2218Vector × Fin 3

def r2218LayerAdd (i j : Fin 3) : Fin 3 :=
  ⟨(i.val + j.val) % 3, by omega⟩

def r2218LayerNeg (i : Fin 3) : Fin 3 :=
  ⟨(3 - i.val) % 3, by omega⟩

def r2218LayerScalar (i : Fin 3) : R2218F7 :=
  (2 : R2218F7) ^ i.val

def r2218Mul (g h : R2218G) : R2218G :=
  (fun k => g.1 k + r2218LayerScalar g.2 * h.1 k,
    r2218LayerAdd g.2 h.2)

def r2218Inv (g : R2218G) : R2218G :=
  (fun k => -((2 : R2218F7) ^ ((3 - g.2.val) % 3)) * g.1 k,
    r2218LayerNeg g.2)

def r2218EmbedV (v : R2218Vector) : R2218G :=
  (v, ⟨0, by omega⟩)

def r2218C : R2218G :=
  (0, ⟨1, by omega⟩)

def r2218Double (v : R2218Vector) : R2218Vector :=
  fun k => (2 : R2218F7) * v k

def r2218Shear (v : R2218Vector) : R2218Vector :=
  fun k =>
    if k = (0 : Fin 3) then v 0
    else if k = (1 : Fin 3) then v 1
    else v 2 + v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2

def r2218ShearInv (v : R2218Vector) : R2218Vector :=
  fun k =>
    if k = (0 : Fin 3) then v 0
    else if k = (1 : Fin 3) then v 1
    else v 2 - v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2

def r2218F (g : R2218G) : R2218G :=
  (r2218Shear g.1, g.2)

def r2218FInv (g : R2218G) : R2218G :=
  (r2218ShearInv g.1, g.2)

def r2218RightRegular (g : R2218G) (x : R2218G) : R2218G :=
  r2218Mul x g

def r2218T (g : R2218G) (x : R2218G) : R2218G :=
  r2218F (r2218RightRegular g (r2218FInv x))

def r2218FixedGroupAndShear : Prop :=
  (∀ v : R2218Vector,
    r2218Mul (r2218Mul r2218C (r2218EmbedV v)) (r2218Inv r2218C) =
      r2218EmbedV (r2218Double v)) ∧
  (∀ g : R2218G,
    r2218FInv (r2218F g) = g ∧ r2218F (r2218FInv g) = g) ∧
  (∀ g x : R2218G,
    r2218T g x = r2218F (r2218RightRegular g (r2218FInv x)))

end MathlibPlus.Open.Research
