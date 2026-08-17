import Mathlib

namespace MathlibPlus.Open.Algebra.Claim20551_20552

noncomputable section

open scoped BigOperators

abbrev Root := Fin 3
abbrev Cell := Finset Root
abbrev CellPolynomial (R : Type*) [CommSemiring R] := MvPolynomial Cell R
abbrev HarmonicPolynomial (R : Type*) [CommSemiring R] := MvPolynomial (Fin 7) R

def cellVariable {R : Type*} [CommSemiring R] (S : Cell) : CellPolynomial R :=
  MvPolynomial.X S

def harmonicCell (i : Fin 7) : Cell :=
  ![{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}] i

def harmonicLift {R : Type*} [CommRing R] :
    HarmonicPolynomial R →+* CellPolynomial R :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun i : Fin 7 => cellVariable (harmonicCell i) - cellVariable ∅)

def h3Cell {R : Type*} [CommRing R] : CellPolynomial R :=
  -cellVariable ∅ + cellVariable {0} + cellVariable {1} + cellVariable {2} -
      cellVariable {0, 1} - cellVariable {0, 2} - cellVariable {1, 2} +
      cellVariable {0, 1, 2}

def harmonicAmbiguity {R : Type*} [CommRing R]
    (C : HarmonicPolynomial R) : CellPolynomial R :=
  h3Cell * harmonicLift C

def cardSummationDerivative {R : Type*} [CommRing R]
    (p : CellPolynomial R) : CellPolynomial R :=
  ∑ S : Cell, (MvPolynomial.pderiv S) p

def forgetRoot {R : Type*} [CommRing R] (j : Root) :
    CellPolynomial R →ₐ[R] CellPolynomial R :=
  MvPolynomial.rename (fun S : Cell => S.erase j)

/-- Claim 20551: the three-root Möbius interaction is killed by card
summation and by every separate one-root forgetting map. -/
def claim20551_h3InvisibleToLowerRootMarginals {R : Type*} [CommRing R] : Prop :=
  cardSummationDerivative (h3Cell (R := R)) = 0 ∧
    ∀ j : Root, forgetRoot j (h3Cell (R := R)) = 0

/-- Claim 20552: at every order at least four, multiplying the three-root
interaction by a homogeneous polynomial in the seven harmonic variables gives
another common kernel element. -/
def claim20552_allOrderHarmonicAmbiguities {R : Type*} [CommRing R] : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ∀ C : HarmonicPolynomial R,
      C.IsHomogeneous (n - 4) →
        cardSummationDerivative (harmonicAmbiguity C) = 0 ∧
          ∀ j : Root, forgetRoot j (harmonicAmbiguity C) = 0

end

end MathlibPlus.Open.Algebra.Claim20551_20552
