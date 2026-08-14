import Mathlib

namespace MathlibPlus.Open.Q12Cayley

abbrev Q12 := ZMod 6 × ZMod 2
abbrev C7Q12 := ZMod 7 × Q12

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + (-1 : ZMod 6) ^ x.2.val * y.1 +
      (3 : ZMod 6) * (x.2.val : ZMod 6) * (y.2.val : ZMod 6),
    x.2 + y.2)

def q12One : Q12 := (0, 0)

def q12Inv (x : Q12) : Q12 :=
  ((-1 : ZMod 6) ^ x.2.val *
      (-x.1 - (3 : ZMod 6) * (x.2.val : ZMod 6)), x.2)

def productMul (x y : C7Q12) : C7Q12 :=
  (x.1 + y.1, q12Mul x.2 y.2)

def productOne : C7Q12 := (0, q12One)

def productInv (x : C7Q12) : C7Q12 :=
  (-x.1, q12Inv x.2)

def z : Q12 := (3, 0)

def T₀ : Set Q12 := {(1, 0), (2, 0), (4, 0), (5, 0)}

def connectionSet : Set C7Q12 :=
  {x | x.1 ≠ 0} ∪ {x | x.1 = 0 ∧ x.2 ∈ T₀}

def cayleyAdj (x y : C7Q12) : Prop :=
  productMul (productInv x) y ∈ connectionSet

noncomputable def neighbors (x : C7Q12) : Finset C7Q12 := by
  classical
  exact Finset.univ.filter (fun y => cayleyAdj x y)

def q12GroupLaws : Prop :=
  (∀ x y w : Q12, q12Mul (q12Mul x y) w = q12Mul x (q12Mul y w)) ∧
    (∀ x : Q12, q12Mul q12One x = x) ∧
    (∀ x : Q12, q12Mul x q12One = x) ∧
    (∀ x : Q12, q12Mul (q12Inv x) x = q12One) ∧
    (∀ x : Q12, q12Mul x (q12Inv x) = q12One)

def productGroupLaws : Prop :=
  (∀ x y w : C7Q12, productMul (productMul x y) w = productMul x (productMul y w)) ∧
    (∀ x : C7Q12, productMul productOne x = x) ∧
    (∀ x : C7Q12, productMul x productOne = x) ∧
    (∀ x : C7Q12, productMul (productInv x) x = productOne) ∧
    (∀ x : C7Q12, productMul x (productInv x) = productOne)

/-- Claim 57646: the displayed finite Cayley construction has the stated properties. -/
def claim_57646 : Prop :=
  q12GroupLaws ∧
    productGroupLaws ∧
    (Fintype.card C7Q12 = 84) ∧
    (productOne ∉ connectionSet) ∧
    (∀ s, s ∈ connectionSet → productInv s ∈ connectionSet) ∧
    (∀ x y : C7Q12, Relation.ReflTransGen cayleyAdj x y) ∧
    (∀ x : C7Q12, (neighbors x).card = 76)

end MathlibPlus.Open.Q12Cayley
