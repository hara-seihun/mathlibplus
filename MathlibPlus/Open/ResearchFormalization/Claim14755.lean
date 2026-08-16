import MathlibPlus.Open.AlgebraicPauli.Orientation

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.AlgebraicPauli

/--
Claim 14755.  The character is the weight character of the exact
`Sym^k (ℂ²)` carrier and the displayed finite current is its squared
alignment difference after the stated exponential substitutions.
-/
def squaredAlignmentDifferenceIsHarmonicOddCurrent : Prop :=
  ∀ (k : ℕ) (U Φ : ℝ),
    let y := Complex.exp ((U : ℂ) / 2)
    let α := Complex.exp (Complex.I * (Φ : ℂ) / 2)
    (character k (y * α) ^ 2 - character k (y * α⁻¹) ^ 2) /
        (4 * Complex.I) =
      oddCurrentRightHandSide k U Φ

end
end MathlibPlus.Open.ResearchFormalization
