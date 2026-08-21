import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

/-- Polynomials over `ZMod 2`, the ambient ring for the R1540 arm calculus. -/
abbrev F2Poly := Polynomial (ZMod 2)

/-- The exact arm polynomial of a leg of length `L`. -/
def armF (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.Icc 1 L,
    Polynomial.C ((L - k + 1 : ℕ) : ZMod 2) *
      (Polynomial.X : F2Poly) ^ k

/-- The all-ones arm polynomial of a leg of length `L`. -/
def armJ (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.range (L + 1),
    (Polynomial.X : F2Poly) ^ k

/-- The connected-subtree polynomial of a triple of legs. -/
def connectedArmPolynomial (a b c : ℕ) : F2Poly :=
  armF a + armF b + armF c +
    Polynomial.X * armJ a * armJ b * armJ c

/-- The folded pair of a leg `L` at total weight `w`. -/
def foldedPair (w L : ℕ) : F2Poly :=
  (Polynomial.X : F2Poly) ^ (L + 3) +
    Polynomial.X ^ (w - L + 3)

/-- The folded transform of a triple of legs at total weight `w`. -/
def foldedArmPolynomial (w a b c : ℕ) : F2Poly :=
  foldedPair w a + foldedPair w b + foldedPair w c

end

end MathlibPlus.Open.Combinatorics.R1540
