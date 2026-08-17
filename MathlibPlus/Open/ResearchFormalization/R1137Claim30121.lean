import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim30121

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

def q12T90 : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

def q12T90Inv : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

def alpha12T90 : A4Coordinates → A4Coordinates :=
  ![0, 2, 1, 3, 5, 4, 9, 10, 11, 6, 7, 8]

def identityA4 : A4Coordinates := 0

def involutionSet : Set A4Coordinates := {3, 8, 11}

def orderThreeSet : Set A4Coordinates := {1, 2, 4, 5, 6, 7, 9, 10}

def transportedMul (r k : A4Coordinates) : A4Coordinates :=
  q12T90Inv (a4Mul (q12T90 r) (q12T90 k))

def transportedInv (r : A4Coordinates) : A4Coordinates :=
  q12T90Inv (a4Inv (q12T90 r))

def transportedGenerationStep (S : Set A4Coordinates)
    (r s : A4Coordinates) : Prop :=
  ∃ k : A4Coordinates, k ∈ S ∧
    (s = transportedMul r k ∨ s = transportedMul r (transportedInv k))

def transportedGeneratedBy (S : Set A4Coordinates) : Set A4Coordinates :=
  {r | Relation.ReflTransGen (transportedGenerationStep S) identityA4 r}

def transportedOrderThree (r : A4Coordinates) : Prop :=
  r ≠ identityA4 ∧
    transportedMul r r ≠ identityA4 ∧
    transportedMul (transportedMul r r) r = identityA4

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

/-- The relative derivative uses the lifted source action on the vertex. -/
def affineRelativeDerivative {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (x : ZMod p) (h : A4Coordinates)
    (y : ZMod p) (k : A4Coordinates) : PrimeProduct p :=
  affineLiftInv lambda tau
    (productMul
      (affineLift lambda tau (productMul (x, h) (y, k)))
      (productInv (affineLift lambda tau (y, k))))

def sourceInversion {p : ℕ} (z : PrimeProduct p) : PrimeProduct p :=
  (-z.1, a4Inv z.2)

def derivativeStep {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (z w : PrimeProduct p) : Prop :=
  ∃ (x y : ZMod p) (h k : A4Coordinates),
    z = (x, h) ∧ w = affineRelativeDerivative lambda tau x h y k

def compatibilityStep {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (z w : PrimeProduct p) : Prop :=
  derivativeStep lambda tau z w ∨
    w = sourceInversion z ∨ z = sourceInversion w

def compatibilityOrbit {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (z : PrimeProduct p) : Set (PrimeProduct p) :=
  {w | Relation.ReflTransGen (compatibilityStep lambda tau) z w}

def saturatedPrimeFiber {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p)
    (r : A4Coordinates) : Prop :=
  ∀ x : ZMod p,
    (x, r) ∈ compatibilityOrbit lambda tau (0, r)

def scalarPeriodSet {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ) : Set A4Coordinates :=
  {r | ∀ k : A4Coordinates,
    lambda (transportedMul r k) = lambda k}

def scalarDifferenceSuppliesEveryTranslation {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (r k : A4Coordinates) : Prop :=
  ∀ t : ZMod p, ∃ y : ZMod p,
    ((lambda (transportedMul r k) : ZMod p) - (lambda k : ZMod p)) * y = t

def betaPlus {p : ℕ} : PrimeProduct p → PrimeProduct p :=
  fun z => (z.1, alpha12T90 z.2)

def nonconstantScalarProfile {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ) : Prop :=
  ¬ ∃ c : (ZMod p)ˣ, ∀ h : A4Coordinates, lambda h = c

def transportedOrderThreeSet : Set A4Coordinates :=
  {r | transportedOrderThree r}

/-- Claim 30121: nonconstant scalar profiles saturate the order-three and
involution fibres, with the scalar-period translation exception and its
`β₊` agreement exactly as stated. -/
def nonconstantScalarProfilesSaturateRelevantFibres : Prop :=
  transportedOrderThreeSet = orderThreeSet ∧
    transportedGeneratedBy orderThreeSet = Set.univ ∧
    ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
      ∀ (lambda : A4Coordinates → (ZMod p)ˣ)
        (tau : A4Coordinates → ZMod p),
        lambda identityA4 = 1 → tau identityA4 = 0 →
        (nonconstantScalarProfile lambda →
          (∃ (r k : A4Coordinates),
            transportedOrderThree r ∧ r ∉ scalarPeriodSet lambda ∧
              ((lambda (transportedMul r k) : ZMod p) -
                  (lambda k : ZMod p)) ≠ 0 ∧
              scalarDifferenceSuppliesEveryTranslation lambda r k) ∧
          (∀ r : A4Coordinates, r ∈ transportedOrderThreeSet →
            saturatedPrimeFiber lambda tau r)) ∧
        (∀ r : A4Coordinates, r ∈ involutionSet →
          (r ∉ scalarPeriodSet lambda →
            saturatedPrimeFiber lambda tau r) ∧
          (r ∈ scalarPeriodSet lambda →
            (∀ (x y : ZMod p),
              affineRelativeDerivative lambda tau x r y r =
                (x - 2 * tau r, r)) ∧
            ((tau r ≠ 0 → saturatedPrimeFiber lambda tau r) ∧
              (tau r = 0 →
                ∀ x : ZMod p,
                  affineLift lambda tau (x, r) =
                    betaPlus (x, r)))))

end MathlibPlus.Open.ResearchFormalization.R1137Claim30121
