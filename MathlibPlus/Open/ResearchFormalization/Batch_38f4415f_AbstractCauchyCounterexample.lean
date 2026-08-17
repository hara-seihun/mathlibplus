import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.AbstractCauchyCounterexample

abbrev PairStatePolynomial := Polynomial (Polynomial ℚ)

def shiftedCavity (a : ℚ) : Polynomial ℚ :=
  Polynomial.X + Polynomial.C a

def pairStateFactor (a b : ℚ) : PairStatePolynomial :=
  Polynomial.X + Polynomial.C (shiftedCavity a * shiftedCavity b)

def matchingPolynomial (a b c d : ℚ) : PairStatePolynomial :=
  pairStateFactor a b * pairStateFactor c d

/-- The three perfect matchings on the four scalar cavities 1, 2, 3, 4
    satisfy a nontrivial affine relation. -/
def claim24637 : Prop :=
  matchingPolynomial 1 2 3 4 -
      4 * matchingPolynomial 1 3 2 4 +
      3 * matchingPolynomial 1 4 2 3 = 0

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.AbstractCauchyCounterexample
