import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffedbA62472678ab91c09276f01d0

noncomputable section

abbrev HarmonicVar := Fin 7

-- Variable assignment: P=0, Q=1, A=2, B=3, M=4, C=5, D=6.
def P : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 0
def Q : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 1
def A : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 2
def B : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 3
def M : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 4
def C : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 5
def D : MvPolynomial HarmonicVar ℤ := MvPolynomial.X 6

def vandermondeR : MvPolynomial HarmonicVar ℤ :=
  (C - D) * (C - M) * (D - M)

def vandermondeL : MvPolynomial HarmonicVar ℤ :=
  (A - B) * (A - M) * (B - M)

def psiR : MvPolynomial HarmonicVar ℤ :=
  P * Q ^ 2 * vandermondeR * (A - B + P) *
    (C ^ 2 + D ^ 2 + M ^ 2 - Q ^ 2)

def psiL : MvPolynomial HarmonicVar ℤ :=
  P ^ 2 * Q * vandermondeL * (C - D - Q) *
    (A ^ 2 + B ^ 2 + M ^ 2 - P ^ 2)

/-- Claim 5268: the two edge-14 alternating face harmonics have the stated
integer polynomial forms, 54 nonzero integer coefficients each, and their
Vandermonde factors retain dependence on the middle-arm variable M. -/
def claim5268 : Prop :=
  psiR.support.card = 54 ∧
  psiL.support.card = 54 ∧
  MvPolynomial.degreeOf (4 : HarmonicVar) vandermondeR = 2 ∧
  MvPolynomial.degreeOf (4 : HarmonicVar) vandermondeL = 2

end

end MathlibPlus.Open.ResearchFormalization.Batch019ffedbA62472678ab91c09276f01d0
