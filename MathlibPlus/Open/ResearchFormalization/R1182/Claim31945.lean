import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31945

abbrev Q12 := ZMod 3 × ZMod 4

def q12Parity (i : ZMod 4) : ZMod 3 :=
  (-1 : ZMod 3) ^ i.val

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + q12Parity x.2 * y.1, x.2 + y.2)

def q12One : Q12 := (0, 0)

def q12Sigma (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (1, 3)
  else if x = ((1, 3) : Q12) then (2, 2)
  else if x = ((2, 2) : Q12) then (1, 1)
  else if x = ((2, 1) : Q12) then (1, 2)
  else if x = ((1, 2) : Q12) then (2, 3)
  else if x = ((2, 3) : Q12) then (2, 1)
  else x

def q12SigmaInv (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (2, 2)
  else if x = ((1, 3) : Q12) then (1, 1)
  else if x = ((2, 2) : Q12) then (1, 3)
  else if x = ((2, 1) : Q12) then (2, 3)
  else if x = ((1, 2) : Q12) then (2, 1)
  else if x = ((2, 3) : Q12) then (1, 2)
  else x

def q12Automorphism (f : Q12 → Q12) : Prop :=
  Function.Bijective f ∧
    ∀ x y : Q12, f (q12Mul x y) = q12Mul (f x) (f y)

def negateFirst : Q12 → Q12 :=
  fun x => (-x.1, x.2)

def invertCyclicCoordinate : Q12 → Q12 :=
  fun x => (x.1, -x.2)

def claim31945 : Prop :=
  q12Automorphism negateFirst ∧
    q12Automorphism invertCyclicCoordinate ∧
    (∀ x : Q12,
      q12SigmaInv (q12Sigma x) = x ∧
        q12Sigma (q12SigmaInv x) = x) ∧
    (∀ x : Q12,
      negateFirst (q12Sigma (negateFirst x)) = q12SigmaInv x) ∧
    (∀ x : Q12,
      invertCyclicCoordinate (q12Sigma (invertCyclicCoordinate x)) =
        q12SigmaInv x)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31945
