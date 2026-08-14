import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch

noncomputable section

/-- The formal variables used by the ordered branch-three chart. -/
abbrev BranchThreePolynomial := MvPolynomial (Fin 7) ℤ

def branchThreeP : BranchThreePolynomial := MvPolynomial.X (0 : Fin 7)
def branchThreeA : BranchThreePolynomial := MvPolynomial.X (1 : Fin 7)
def branchThreeB : BranchThreePolynomial := MvPolynomial.X (2 : Fin 7)
def branchThreeM : BranchThreePolynomial := MvPolynomial.X (3 : Fin 7)
def branchThreeQ : BranchThreePolynomial := MvPolynomial.X (4 : Fin 7)
def branchThreeC : BranchThreePolynomial := MvPolynomial.X (5 : Fin 7)
def branchThreeD : BranchThreePolynomial := MvPolynomial.X (6 : Fin 7)

def branchThreeSigmaL : BranchThreePolynomial :=
  branchThreeB - branchThreeA - branchThreeP

def branchThreeSigmaR : BranchThreePolynomial :=
  branchThreeD - branchThreeC + branchThreeQ

/-- Claim 5265: the positive coordinate chart, its shifts, and its corner symbols. -/
def orderedBranchThreeChart
    (p a b m q c d A B M C D : ℕ)
    (sigmaL sigmaR : BranchThreePolynomial) : Prop :=
  0 < p ∧ 0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < q ∧ 0 < c ∧ 0 < d ∧
    A = a - 1 ∧ B = b - 1 ∧ M = m - 1 ∧
    C = c - 1 ∧ D = d - 1 ∧
    sigmaL = branchThreeSigmaL ∧ sigmaR = branchThreeSigmaR

/-- Formal coefficient vectors with bracket labels [u,v,w]. -/
abbrev OuterBlockIndex := ℕ × ℕ × ℕ

def bracket (u v w : ℕ) : Finsupp OuterBlockIndex ℤ :=
  Finsupp.single (u, v, w) 1

abbrev OneSidedPolynomial := MvPolynomial (Fin 3) ℤ

def oneSidedP : OneSidedPolynomial := MvPolynomial.X (0 : Fin 3)
def oneSidedA : OneSidedPolynomial := MvPolynomial.X (1 : Fin 3)
def oneSidedB : OneSidedPolynomial := MvPolynomial.X (2 : Fin 3)

def oneSidedSigma : OneSidedPolynomial :=
  oneSidedB - oneSidedA - oneSidedP

def oneSidedCornerVector (i : ℕ) : Finsupp OuterBlockIndex ℤ :=
  bracket i 1 2 - bracket i 2 1 - bracket (i + 1) 1 1

/-- Claim 5293: the shifted one-sided symbol and its coefficient vector. -/
def oneSidedCornerSymbolClaim
    (i a b A B : ℕ)
    (sigma : OneSidedPolynomial)
    (coefficientVector : Finsupp OuterBlockIndex ℤ) : Prop :=
  1 ≤ i ∧ A = a - 1 ∧ B = b - 1 ∧
    sigma = oneSidedSigma ∧ coefficientVector = oneSidedCornerVector i

/-- Claim 5305: the ordered branch-four path coordinate chart. -/
def orderedBranchFourPathChart
    (x a b m y n z c d : ℕ) : Prop :=
  0 < x ∧ 0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < y ∧
    0 < n ∧ 0 < z ∧ 0 < c ∧ 0 < d

abbrev BranchThreeCard := Fin 7 → ℕ

def curvatureCardBend : BranchThreeCard :=
  ![1, 1, 2, 1, 2, 1, 4]

def curvatureCardLeaf : BranchThreeCard :=
  ![1, 1, 2, 1, 1, 2, 4]

def curvatureCardQuad : BranchThreeCard :=
  ![1, 1, 2, 1, 1, 1, 5]

/-- Claim 5316: the three explicit ordered branch-three curvature cards. -/
def explicitCurvatureCards
    (bend leaf quad : BranchThreeCard) : Prop :=
  bend = curvatureCardBend ∧ leaf = curvatureCardLeaf ∧ quad = curvatureCardQuad

end

end MathlibPlus.Open.ResearchFormalization.Batch
