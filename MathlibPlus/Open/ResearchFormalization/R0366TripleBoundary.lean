import Mathlib

open scoped BigOperators
open Classical

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0366TripleBoundary

abbrev Cell (ι : Type*) := Finset ι
abbrev NonemptyCell (ι : Type*) := {S : Cell ι // S.Nonempty}
abbrev CellPolynomial (ι : Type*) := MvPolynomial (Cell ι) ℚ
abbrev ProfileFamily (ι : Type*) :=
  SimpleGraph ι → CellPolynomial ι

/-- The complete outside-neighborhood cell of a vertex relative to an ordered
root. -/
def neighborhoodCell {V ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (x : ι → V) (v : V) : Cell ι :=
  Finset.univ.filter (fun i => G.Adj (x i) v)

/-- The labeled internal graph condition retained by the complete profile. -/
def rootInternalPredicate {V ι : Type*}
    (G : SimpleGraph V) (A : SimpleGraph ι) (x : ι → V) : Prop :=
  Function.Injective x ∧
    ∀ i k, A.Adj i k ↔ G.Adj (x i) (x k)

/-- The complete profile generating polynomial, including the empty cell. -/
def profilePolynomial {n : ℕ} {ι : Type*} [Fintype ι]
    (G : SimpleGraph (Fin n)) (A : SimpleGraph ι) : CellPolynomial ι :=
  ∑ x : {x : ι → Fin n // rootInternalPredicate G A x},
    ∏ v : {v : Fin n // v ∉ Set.range x.1},
      MvPolynomial.X (neighborhoodCell G x.1 v.1)

/-- The complete profile family indexed by the labeled internal root graph. -/
def profileFamily {n : ℕ} {ι : Type*} [Fintype ι]
    (G : SimpleGraph (Fin n)) : ProfileFamily ι :=
  fun A => profilePolynomial G A

/-- The card-sum directional derivative on the complete cell polynomial. -/
def cardSumDerivative {ι : Type*} [Fintype ι]
    (P : CellPolynomial ι) : CellPolynomial ι :=
  ∑ S : Cell ι, MvPolynomial.pderiv S P

/-- Restrict an internal root graph after deleting one labeled root. -/
abbrev Retained (ι : Type*) (j : ι) := {i : ι // i ≠ j}

def restrictedInternalGraph {ι : Type*} (j : ι)
    (A : SimpleGraph ι) : SimpleGraph (Retained ι j) :=
  SimpleGraph.comap (fun i : Retained ι j => i.1) A

/-- A cell after forgetting a root, in the separate lower-root carrier. -/
def retainedCell {ι : Type*} [Fintype ι]
    (j : ι) (S : Cell ι) : Finset (Retained ι j) :=
  Finset.univ.filter (fun i => i.1 ∈ S)

/-- The coordinate part of a root-forgetting map.  It coalesces a cell with
its cell obtained by deleting the forgotten root label. -/
def rootForgettingPolynomial {ι : Type*} [Fintype ι]
    (j : ι) (P : CellPolynomial ι) :
    MvPolynomial (Finset (Retained ι j)) ℚ :=
  MvPolynomial.rename (fun S => retainedCell j S) P

/-- The full lower-root family map sums all labeled internal root graphs whose
restriction is the retained internal graph. -/
def fullRootForgettingFamily {ι : Type*} [Fintype ι]
    (Q : ProfileFamily ι) (j : ι) :
    ProfileFamily (Retained ι j) :=
  fun B =>
    ∑ A : SimpleGraph ι,
      if restrictedInternalGraph j A = B then
        rootForgettingPolynomial j (Q A)
      else 0

/-- The empty-cell boundary of a complete cell polynomial. -/
def boundaryRestriction {ι : Type*} [Fintype ι]
    (P : CellPolynomial ι) :
    MvPolynomial (NonemptyCell ι) ℚ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun S : Cell ι =>
      if h : S.Nonempty then MvPolynomial.X ⟨S, h⟩ else 0) P

/-- The harmonic lift from nonempty-cell variables. -/
def harmonicLift {ι : Type*} [Fintype ι]
    (C : MvPolynomial (NonemptyCell ι) ℚ) : CellPolynomial ι :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun S : NonemptyCell ι =>
      MvPolynomial.X S.1 - MvPolynomial.X ∅) C

def harmonicCoordinate {ι : Type*}
    (S : Cell ι) : CellPolynomial ι :=
  MvPolynomial.X S - MvPolynomial.X ∅

/-- The boundary of a family is retained componentwise in its internal-graph
carrier. -/
def boundaryFamily {ι : Type*} [Fintype ι]
    (Q : ProfileFamily ι) :
    SimpleGraph ι → MvPolynomial (NonemptyCell ι) ℚ :=
  fun A => boundaryRestriction (Q A)

def zeroProfileFamily {ι : Type*} : ProfileFamily ι :=
  fun _ => 0

/-- A family supported at one labeled internal root graph. -/
def componentProfileFamily
    (A₀ : SimpleGraph (Fin 3))
    (P : CellPolynomial (Fin 3)) : ProfileFamily (Fin 3) :=
  fun A => if A = A₀ then P else 0

/-- The three-way Möbius interaction in the stated harmonic coordinates. -/
def hThree : CellPolynomial (Fin 3) :=
  harmonicCoordinate ({0} : Cell (Fin 3)) +
    harmonicCoordinate ({1} : Cell (Fin 3)) +
    harmonicCoordinate ({2} : Cell (Fin 3)) -
    harmonicCoordinate ({0, 1} : Cell (Fin 3)) -
    harmonicCoordinate ({0, 2} : Cell (Fin 3)) -
    harmonicCoordinate ({1, 2} : Cell (Fin 3)) +
    harmonicCoordinate (Finset.univ : Cell (Fin 3))

/-- The complete one-, two-, and three-step lower-root marginal data. -/
def sameCompleteLowerRootData
    (Q R : ProfileFamily (Fin 3)) : Prop :=
  (∀ A : SimpleGraph (Fin 3),
    cardSumDerivative (Q A) = cardSumDerivative (R A)) ∧
    (∀ (j : Fin 3) (B : SimpleGraph (Retained (Fin 3) j)),
      fullRootForgettingFamily Q j B =
        fullRootForgettingFamily R j B) ∧
    (∀ (j : Fin 3) (k : Retained (Fin 3) j)
      (B : SimpleGraph (Retained (Retained (Fin 3) j) k)),
      fullRootForgettingFamily (fullRootForgettingFamily Q j) k B =
        fullRootForgettingFamily (fullRootForgettingFamily R j) k B) ∧
    (∀ (j : Fin 3) (k : Retained (Fin 3) j)
      (l : Retained (Retained (Fin 3) j) k)
      (B : SimpleGraph
        (Retained (Retained (Retained (Fin 3) j) k) l)),
      fullRootForgettingFamily
          (fullRootForgettingFamily (fullRootForgettingFamily Q j) k) l B =
        fullRootForgettingFamily
          (fullRootForgettingFamily (fullRootForgettingFamily R j) k) l B)

/-- Claim 20489: the exact internal-graph-indexed profile family has a
nonzero all-order harmonic member whose card-sum equations, complete lower-root
profiles, and every iterated full root-forgetting marginal agree with zero,
while its dominating ordered-triple boundary differs. -/
def claim20489 : Prop :=
  ∀ (n : ℕ), 4 ≤ n →
    ∀ C : MvPolynomial (NonemptyCell (Fin 3)) ℚ,
      MvPolynomial.IsHomogeneous C (n - 4) → C ≠ 0 →
        ∀ A₀ : SimpleGraph (Fin 3),
          let B := hThree * harmonicLift C
          let Q := componentProfileFamily A₀ B
          B ≠ 0 ∧
            MvPolynomial.IsHomogeneous B (n - 3) ∧
            sameCompleteLowerRootData Q zeroProfileFamily ∧
            boundaryFamily Q ≠ boundaryFamily zeroProfileFamily

end MathlibPlus.Open.ResearchFormalization.R0366TripleBoundary
