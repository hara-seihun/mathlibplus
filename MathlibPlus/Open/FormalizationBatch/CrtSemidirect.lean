import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

abbrev r2282Carrier := ZMod 91 × ZMod 3

def r2282Multiplication (α : ZMod 91) (g h : r2282Carrier) : r2282Carrier :=
  (g.1 + α ^ g.2.val * h.1, g.2 + h.2)

def r2282FixedPointFree (α : ZMod 91) : Prop :=
  ∀ k : ZMod 3, k ≠ 0 →
    ∀ x : ZMod 91, α ^ k.val * x = x → x = 0

def r2282CRTRepresentative (α : ZMod 91) (u v : ℕ) : Prop :=
  ZMod.val α % 7 = u % 7 ∧ ZMod.val α % 13 = v % 13

def r2282Identity : r2282Carrier := (0, 0)

def r2282GroupLaw (α : ZMod 91) : Prop :=
  ∃ (inverse : r2282Carrier → r2282Carrier),
    (∀ x y z : r2282Carrier,
      r2282Multiplication α (r2282Multiplication α x y) z =
        r2282Multiplication α x (r2282Multiplication α y z)) ∧
    (∀ x : r2282Carrier,
      r2282Multiplication α r2282Identity x = x ∧
      r2282Multiplication α x r2282Identity = x ∧
      r2282Multiplication α x (inverse x) = r2282Identity ∧
      r2282Multiplication α (inverse x) x = r2282Identity) ∧
    Fintype.card r2282Carrier = 273 ∧
    Fintype.card {x : r2282Carrier // x ≠ r2282Identity} = 272

def r2282Power (α : ZMod 91) (x : r2282Carrier) : ℕ → r2282Carrier
  | 0 => r2282Identity
  | n + 1 => r2282Multiplication α (r2282Power α x n) x

def r2282PresentationRelations (α : ZMod 91) : Prop :=
  let a : r2282Carrier := (1, 0)
  let t : r2282Carrier := (0, 2)
  let tinv : r2282Carrier := (0, 1)
  r2282Power α a 91 = r2282Identity ∧
  r2282Power α t 3 = r2282Identity ∧
  r2282Multiplication α tinv t = r2282Identity ∧
  r2282Multiplication α t tinv = r2282Identity ∧
  r2282Multiplication α
      (r2282Multiplication α tinv a) t =
    r2282Power α a (ZMod.val α) ∧
  ∀ x : r2282Carrier, ∃ m n : ℕ,
    x = r2282Multiplication α (r2282Power α a m) (r2282Power α t n)

def r2282OrderThree (α : ZMod 91) : Prop :=
  α ^ 3 = 1 ∧ α ≠ 1

def claim43843 : Prop :=
  let aligned : ZMod 91 := 16
  let opposite : ZMod 91 := 9
  aligned = 16 ∧
  opposite = 9 ∧
  r2282CRTRepresentative aligned 2 3 ∧
  r2282CRTRepresentative opposite 2 9 ∧
  ∀ α : ZMod 91, α = aligned ∨ α = opposite →
    r2282GroupLaw α ∧ r2282FixedPointFree α

def claim43891 : Prop :=
  let aligned : ZMod 91 := 16
  let opposite : ZMod 91 := 9
  aligned = 16 ∧
  opposite = 9 ∧
  r2282CRTRepresentative aligned 2 3 ∧
  r2282CRTRepresentative opposite 2 9 ∧
  ∀ α : ZMod 91, α = aligned ∨ α = opposite →
    r2282GroupLaw α ∧
    r2282PresentationRelations α ∧
    r2282OrderThree α ∧
    r2282FixedPointFree α

end MathlibPlus.Open.FormalizationBatch
