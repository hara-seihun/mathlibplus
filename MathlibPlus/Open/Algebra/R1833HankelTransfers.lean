import Mathlib

namespace MathlibPlus.Open.Algebra.R1833

noncomputable section

/-- The exact polynomial carrier with one root variable z and the variables x_k. -/
abbrev HankelRing := MvPolynomial (Option ℕ) ℤ

def zVar : HankelRing := MvPolynomial.X none

def xVar (k : ℕ) : HankelRing := MvPolynomial.X (some k)

/-- The pairwise Koszul transfer and its first-selector Hankel image. -/
def pairTransfer (a b : ℕ) : HankelRing :=
  zVar ^ a * xVar (b + 2) - zVar ^ b * xVar (a + 2)

def hankelMinor (a b : ℕ) : HankelRing :=
  xVar (a + 1) * xVar (b + 2) - xVar (a + 2) * xVar (b + 1)

/-- Every Hankel hexagon is exactly the three-column compatibility relation
among pair transfers. -/
def claim_32737 : Prop :=
  ∀ a b c : ℕ, a < b → b < c →
    zVar ^ a * hankelMinor b c - zVar ^ b * hankelMinor a c +
        zVar ^ c * hankelMinor a b =
      -xVar (c + 1) * pairTransfer a b +
        xVar (b + 1) * pairTransfer a c -
          xVar (a + 1) * pairTransfer b c

end

end MathlibPlus.Open.Algebra.R1833
