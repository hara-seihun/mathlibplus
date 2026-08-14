import Mathlib

namespace MathlibPlus.Open.Research

open MvPolynomial
noncomputable section

abbrev OrderedBranchFourPathPolynomial (R : Type*) [CommSemiring R] :=
  MvPolynomial (Fin 9) R

def orderedPathX {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 0
def orderedPathA {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 1
def orderedPathB {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 2
def orderedPathM {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 3
def orderedPathY {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 4
def orderedPathN {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 5
def orderedPathZ {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 6
def orderedPathC {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 7
def orderedPathD {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R := X 8

def orderedPathSigmaL {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R :=
  orderedPathB - orderedPathA - orderedPathX

def orderedPathSigmaR {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R :=
  orderedPathD - orderedPathC + orderedPathZ

def orderedPathEta {R : Type*} [CommRing R] : OrderedBranchFourPathPolynomial R :=
  orderedPathM - orderedPathN

/-- Claim 5358: the corner-reduced mode has the displayed factorization. -/
def cornerReducedOrderedPathMode {R : Type*} [CommRing R]
    (P ρ : OrderedBranchFourPathPolynomial R) : Prop :=
  P = orderedPathX * orderedPathY * orderedPathZ * orderedPathSigmaL *
      orderedPathSigmaR * ρ

def orderedPathLeftSuspensionFormula {R : Type*} [CommRing R]
    : OrderedBranchFourPathPolynomial R :=
  orderedPathY * orderedPathX ^ 2 * orderedPathZ *
    (orderedPathA - orderedPathB) * (orderedPathA - orderedPathM) *
    (orderedPathB - orderedPathM) * (orderedPathC - orderedPathD - orderedPathZ) *
    (orderedPathA ^ 2 + orderedPathB ^ 2 + orderedPathM ^ 2 - orderedPathX ^ 2)

def orderedPathRightSuspensionFormula {R : Type*} [CommRing R]
    : OrderedBranchFourPathPolynomial R :=
  orderedPathY * orderedPathX * orderedPathZ ^ 2 *
    (orderedPathC - orderedPathD) * (orderedPathC - orderedPathN) *
    (orderedPathD - orderedPathN) * (orderedPathA - orderedPathB + orderedPathX) *
    (orderedPathC ^ 2 + orderedPathD ^ 2 + orderedPathN ^ 2 - orderedPathZ ^ 2)

/-- Claim 5368: both displayed internal-edge suspension formulas. -/
def internalEdgeSuspensionFormulas {R : Type*} [CommRing R]
    (H_L H_R : OrderedBranchFourPathPolynomial R) : Prop :=
  H_L = orderedPathLeftSuspensionFormula ∧
    H_R = orderedPathRightSuspensionFormula

end
end MathlibPlus.Open.Research
