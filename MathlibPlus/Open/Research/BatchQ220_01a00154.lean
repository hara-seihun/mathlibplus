import Mathlib

namespace MathlibPlus.Open.Research

abbrev Q220 := ZMod 11 × ZMod 5 × Fin 4

def q220Mul (a b : Q220) : Q220 :=
  let even : Prop := a.2.2.val % 2 = 0
  let e11 : ZMod 11 := if even then 1 else -1
  let e5 : ZMod 5 := if even then 1 else -1
  (a.1 + e11 * b.1,
    a.2.1 + e5 * b.2.1,
    ⟨(a.2.2.val + b.2.2.val) % 4, by omega⟩)

def q220One : Q220 := (0, 0, 0)

def q220Pow (a : Q220) : Nat → Q220
  | 0 => q220One
  | n + 1 => q220Mul (q220Pow a n) a

def q220HasOrder (a : Q220) (order : Nat) : Prop :=
  q220Pow a order = q220One ∧
    ∀ k : Fin order, 0 < k.val → q220Pow a k.val ≠ q220One

def q220GroupLaw : Prop :=
  (∀ x y z : Q220,
    q220Mul (q220Mul x y) z = q220Mul x (q220Mul y z)) ∧
  (∀ x : Q220,
    q220Mul q220One x = x ∧ q220Mul x q220One = x) ∧
  (∀ x : Q220,
    ∃ y : Q220,
      q220Mul x y = q220One ∧ q220Mul y x = q220One)

def q220Model : Prop :=
  Fintype.card Q220 = 220

def claim_43643 : Prop :=
  q220GroupLaw ∧
    q220Model ∧
    ∃ r s : Q220,
      q220HasOrder r 110 ∧
      q220HasOrder s 4 ∧
      q220Pow s 2 = q220Pow r 55 ∧
      q220Mul s r = q220Mul (q220Pow r 109) s ∧
      ∀ x : Q220,
        ∃ k : Fin 110,
          x = q220Pow r k.val ∨
            x = q220Mul (q220Pow r k.val) s

end MathlibPlus.Open.Research
