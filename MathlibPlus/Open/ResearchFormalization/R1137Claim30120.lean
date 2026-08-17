import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim30120

abbrev A4Coordinates := Fin 12

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

def identityA4 : A4Coordinates := 0

def transportedMul (r k : A4Coordinates) : A4Coordinates :=
  q12T90Inv (a4Mul (q12T90 r) (q12T90 k))

def transportedInv (r : A4Coordinates) : A4Coordinates :=
  q12T90Inv (a4Inv (q12T90 r))

def scalarPeriodSet {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ) : Set A4Coordinates :=
  {r | ∀ k : A4Coordinates,
    lambda (transportedMul r k) = lambda k}

def transportedSubgroup (S : Set A4Coordinates) : Prop :=
  identityA4 ∈ S ∧
    (∀ r s, r ∈ S → s ∈ S → transportedMul r s ∈ S) ∧
    (∀ r, r ∈ S → transportedInv r ∈ S)

def nonconstantScalarProfile {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ) : Prop :=
  ¬ ∃ c : (ZMod p)ˣ, ∀ h : A4Coordinates, lambda h = c

/-- Claim 30120: the scalar-period set is a subgroup of the transported
coordinate group, has scalar one, and is proper for a nonconstant profile. -/
def scalarPeriodSubgroupClaim : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (lambda : A4Coordinates → (ZMod p)ˣ),
      lambda identityA4 = 1 →
      transportedSubgroup (scalarPeriodSet lambda) ∧
        (∀ r : A4Coordinates, r ∈ scalarPeriodSet lambda →
          lambda r = 1) ∧
        (nonconstantScalarProfile lambda →
          scalarPeriodSet lambda ≠ Set.univ)

end MathlibPlus.Open.ResearchFormalization.R1137Claim30120
