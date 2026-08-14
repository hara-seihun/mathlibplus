import Mathlib

namespace MathlibPlus.Open.Edge13

noncomputable section

inductive Variable
  | a
  | b
  | m
  | n
  | c
  | d
  | x
  | y
  | z
  deriving DecidableEq

abbrev Polynomial := MvPolynomial Variable ℤ

def a : Polynomial := MvPolynomial.X .a
def b : Polynomial := MvPolynomial.X .b
def m : Polynomial := MvPolynomial.X .m
def n : Polynomial := MvPolynomial.X .n
def c : Polynomial := MvPolynomial.X .c
def d : Polynomial := MvPolynomial.X .d
def x : Polynomial := MvPolynomial.X .x
def y : Polynomial := MvPolynomial.X .y
def z : Polynomial := MvPolynomial.X .z

def shiftedA : Polynomial := a - MvPolynomial.C 1
def shiftedB : Polynomial := b - MvPolynomial.C 1
def shiftedM : Polynomial := m - MvPolynomial.C 1
def shiftedN : Polynomial := n - MvPolynomial.C 1
def shiftedC : Polynomial := c - MvPolynomial.C 1
def shiftedD : Polynomial := d - MvPolynomial.C 1

def sigmaL : Polynomial := shiftedB - shiftedA - x
def sigmaR : Polynomial := shiftedD - shiftedC + z

def residualBend : Polynomial := x * y * z * (x - y) * (y - z)
def residualLeaf : Polynomial := x * y * z * (shiftedM - shiftedN) * (x - y + z)
def residualQuad : Polynomial := x * y * z * (x ^ 2 - x * z - y ^ 2 + z ^ 2)

def modeBend : Polynomial := sigmaL * sigmaR * residualBend
def modeLeaf : Polynomial := sigmaL * sigmaR * residualLeaf
def modeQuad : Polynomial := sigmaL * sigmaR * residualQuad

def commonFactor : Polynomial := sigmaL * sigmaR * x * y * z

def factorizedModes : Prop :=
  modeBend = sigmaL * sigmaR * residualBend ∧
  modeLeaf = sigmaL * sigmaR * residualLeaf ∧
  modeQuad = sigmaL * sigmaR * residualQuad ∧
  modeBend = commonFactor * ((x - y) * (y - z)) ∧
  modeLeaf = commonFactor * ((shiftedM - shiftedN) * (x - y + z)) ∧
  modeQuad = commonFactor * (x ^ 2 - x * z - y ^ 2 + z ^ 2)

end

end MathlibPlus.Open.Edge13
