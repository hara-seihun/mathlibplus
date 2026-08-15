import Mathlib

namespace MathlibPlus.Open.ChemicalPotential

/--
The exact odd-parity identity from the mesh relation.  The sequences `a`, `r`,
`W`, and `R` are the admitted lifted-coordinate data, while `C` is the first
difference of the boundary-difference sequence `ell`.
-/
def exactOddParityChemicalPotentialIdentity : Prop :=
  ∀ (n k m : ℕ) (a r W R ell C : ℕ → ℝ),
    0 < k →
    m = n - k →
    a (2 * k - 1) = r (k - 1) →
    (∀ j : ℕ, R j = Real.log (8 * Real.pi * a j) + W j) →
    (∀ j : ℕ, C j = ell j - ell (j + 1)) →
    2 * Real.log (r (k - 1)) = C m →
    R (2 * k - 1) =
      Real.log (8 * Real.pi) + W (2 * k - 1) + (1 / 2 : ℝ) * C m

end MathlibPlus.Open.ChemicalPotential
