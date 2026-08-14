import Mathlib

namespace MathlibPlus.Open.Research

namespace P3Contamination

noncomputable section

abbrev Variable := Option ℕ

/-- The component-size variables used by the explicit path-of-three calculation. -/
def x (k : ℕ) : MvPolynomial Variable ℤ := MvPolynomial.X (some k)

def t : MvPolynomial Variable ℤ := MvPolynomial.X none

/-- The four edge-cut cases of the three-vertex path. -/
def uP3ByCuts : MvPolynomial Variable ℤ :=
  x 3 + x 2 * x 1 + x 1 * x 2 + x 1 ^ 3

def uP3 : MvPolynomial Variable ℤ := uP3ByCuts

/-- The alternating derivative transform, with the only nonzero variables of `uP3`. -/
def vP3 : MvPolynomial Variable ℤ :=
  (-t) ^ 1 * MvPolynomial.pderiv (some 1) uP3 +
    (-t) ^ 2 * MvPolynomial.pderiv (some 2) uP3 +
    (-t) ^ 3 * MvPolynomial.pderiv (some 3) uP3

def centroidTerm : MvPolynomial Variable ℤ := -t * (x 1 - t) ^ 2

def nonCentroidTerm : MvPolynomial Variable ℤ := -2 * t * (x 1 ^ 2 + x 2)

/-- The explicit three-vertex contamination witness (R-5080.5). -/
def claim57194 : Prop :=
  uP3 = x 3 + 2 * x 2 * x 1 + x 1 ^ 3 ∧
    vP3 = -t * (3 * x 1 ^ 2 + 2 * x 2) + 2 * t ^ 2 * x 1 - t ^ 3 ∧
    vP3 = centroidTerm + nonCentroidTerm ∧
    nonCentroidTerm ≠ 0

end

end P3Contamination

end MathlibPlus.Open.Research
