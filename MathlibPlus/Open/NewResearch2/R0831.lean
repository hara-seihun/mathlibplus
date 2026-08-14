import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0831

open scoped BigOperators
noncomputable section

abbrev ResidualRing := MvPolynomial (Fin 7) ℤ

private def z : ResidualRing := MvPolynomial.X 0
private def x (i : Fin 6) : ResidualRing := MvPolynomial.X i.succ
private def x1 : ResidualRing := x 0
private def x2 : ResidualRing := x 1
private def x3 : ResidualRing := x 2
private def x4 : ResidualRing := x 3
private def x5 : ResidualRing := x 4
private def x6 : ResidualRing := x 5

def a : ResidualRing := x3 * x5 - x4 ^ 2
def b : ResidualRing := x2 * x5 - x3 * x4
def c : ResidualRing := x2 * x4 - x3 ^ 2
def d : ResidualRing := x3 * x6 - x4 * x5
def e : ResidualRing := x4 ^ 2 - x2 * x6

def K : ResidualRing := z * a - z ^ 2 * b + z ^ 3 * c
def R : ResidualRing := z * d + z ^ 2 * e + z ^ 3 * b

def claim27086 : Prop :=
  a + x4 ^ 2 = x3 * x5 ∧
  b + x3 * x4 = x2 * x5 ∧
  c + x3 ^ 2 = x2 * x4 ∧
  d + x4 * x5 = x3 * x6 ∧
  e + x2 * x6 = x4 ^ 2

def claim27087 : Prop :=
  K = z * a - z ^ 2 * b + z ^ 3 * c ∧
  R = z * d + z ^ 2 * e + z ^ 3 * b

def JOneVertex : ResidualRing := x1 + z

def claim27093 : Prop :=
  JOneVertex = x1 + z

end

end MathlibPlus.Open.NewResearch2.R0831
