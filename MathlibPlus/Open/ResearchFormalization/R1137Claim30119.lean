import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim30119

abbrev A4Coordinates := Fin 12
abbrev PrimeProduct (p : ℕ) := ZMod p × A4Coordinates

/-- The retained one-based `A₄` table, written with zero-based `Fin 12` labels. -/
def a4Mul : A4Coordinates → A4Coordinates → A4Coordinates :=
  ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    ![1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10],
    ![2, 0, 1, 4, 5, 3, 8, 6, 7, 10, 11, 9],
    ![3, 6, 9, 0, 7, 10, 1, 4, 11, 2, 5, 8],
    ![4, 8, 10, 2, 6, 11, 0, 5, 9, 1, 3, 7],
    ![5, 7, 11, 1, 8, 9, 2, 3, 10, 0, 4, 6],
    ![6, 9, 3, 10, 0, 7, 4, 11, 1, 8, 2, 5],
    ![7, 11, 5, 9, 1, 8, 3, 10, 2, 6, 0, 4],
    ![8, 10, 4, 11, 2, 6, 5, 9, 0, 7, 1, 3],
    ![9, 3, 6, 7, 10, 0, 11, 1, 4, 5, 8, 2],
    ![10, 4, 8, 6, 11, 2, 9, 0, 5, 3, 7, 1],
    ![11, 5, 7, 8, 9, 1, 10, 2, 3, 4, 6, 0]
  ]

def a4Inv : A4Coordinates → A4Coordinates :=
  ![0, 2, 1, 3, 6, 9, 4, 10, 8, 5, 7, 11]

/-- The displayed retained coordinate maps, in zero-based form. -/
def q12T90 : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

def q12T90Inv : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

def alpha12T90 : A4Coordinates → A4Coordinates :=
  ![0, 2, 1, 3, 5, 4, 9, 10, 11, 6, 7, 8]

def identityA4 : A4Coordinates := 0

def orderThreeOrbitOne : Set A4Coordinates := {1, 5, 6, 10}

def orderThreeOrbitTwo : Set A4Coordinates := {2, 4, 7, 9}

def transportedMul (r k : A4Coordinates) : A4Coordinates :=
  q12T90Inv (a4Mul (q12T90 r) (q12T90 k))

def projectedDerivative (k h : A4Coordinates) : A4Coordinates :=
  q12T90Inv
    (a4Mul
      (q12T90 (a4Mul h k))
      (a4Inv (q12T90 k)))

def productMul {p : ℕ} (u v : PrimeProduct p) : PrimeProduct p :=
  (u.1 + v.1, a4Mul u.2 v.2)

def productInv {p : ℕ} (u : PrimeProduct p) : PrimeProduct p :=
  (-u.1, a4Inv u.2)

def affineLift {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p) :
    PrimeProduct p → PrimeProduct p :=
  fun z =>
    ((lambda z.2 : ZMod p) * z.1 + tau z.2, q12T90 z.2)

def affineLiftInv {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p) :
    PrimeProduct p → PrimeProduct p :=
  fun z =>
    ((lambda (q12T90Inv z.2) : ZMod p)⁻¹ *
        (z.1 - tau (q12T90Inv z.2)), q12T90Inv z.2)

/-- The derivative applies the lift to the source action on the vertex before
multiplying by the inverse of the lifted vertex. -/
def affineRelativeDerivative {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (x : ZMod p) (h : A4Coordinates)
    (y : ZMod p) (k : A4Coordinates) : PrimeProduct p :=
  affineLiftInv lambda tau
    (productMul
      (affineLift lambda tau (productMul (x, h) (y, k)))
      (productInv (affineLift lambda tau (y, k))))

def affineRelativeDerivativeFormula {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (x : ZMod p) (h : A4Coordinates)
    (y : ZMod p) (k : A4Coordinates) : PrimeProduct p :=
  let r := projectedDerivative k h
  ((lambda r : ZMod p)⁻¹ *
      ((lambda (a4Mul h k) : ZMod p) * x +
        ((lambda (a4Mul h k) : ZMod p) - (lambda k : ZMod p)) * y +
        tau (a4Mul h k) - tau k - tau r), r)

def projectedStep (r s : A4Coordinates) : Prop :=
  ∃ k : A4Coordinates,
    s = projectedDerivative k r ∨ r = projectedDerivative k s

def projectedOrbit (r : A4Coordinates) : Set A4Coordinates :=
  {s | Relation.ReflTransGen projectedStep r s}

def projectedOrbitCensus : Prop :=
  projectedOrbit identityA4 = ({identityA4} : Set A4Coordinates) ∧
    projectedOrbit 1 = orderThreeOrbitOne ∧
    projectedOrbit 2 = orderThreeOrbitTwo ∧
    projectedOrbit 3 = ({3} : Set A4Coordinates) ∧
    projectedOrbit 8 = ({8} : Set A4Coordinates) ∧
    projectedOrbit 11 = ({11} : Set A4Coordinates)

def qAlphaAgreeOnInvolutions : Prop :=
  ∀ h : A4Coordinates, h ∈ ({0, 3, 8, 11} : Set A4Coordinates) →
    q12T90 h = alpha12T90 h

/-- Claim 30119: the source-action relative derivative has the displayed
formula, the projected group has exactly the six retained base orbits, source
inversion swaps the two order-three orbits, and `q` agrees with `α` on the
identity and involutions. -/
def relativeDerivativeFormulaAndProjectedOrbitCensus : Prop :=
  (∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (lambda : A4Coordinates → (ZMod p)ˣ)
      (tau : A4Coordinates → ZMod p),
      lambda identityA4 = 1 → tau identityA4 = 0 →
      ∀ (x y : ZMod p) (h k : A4Coordinates),
        affineRelativeDerivative lambda tau x h y k =
          affineRelativeDerivativeFormula lambda tau x h y k) ∧
  projectedOrbitCensus ∧
  Set.image a4Inv orderThreeOrbitOne = orderThreeOrbitTwo ∧
  Set.image a4Inv orderThreeOrbitTwo = orderThreeOrbitOne ∧
  qAlphaAgreeOnInvolutions

end MathlibPlus.Open.ResearchFormalization.R1137Claim30119
