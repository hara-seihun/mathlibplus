import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

abbrev F2Poly := Polynomial (ZMod 2)

private def armF (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.Icc 1 L,
    Polynomial.C ((L - k + 1 : ℕ) : ZMod 2) *
      (Polynomial.X : F2Poly) ^ k

private def armJ (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.range (L + 1),
    (Polynomial.X : F2Poly) ^ k

/-- Claim 39051: the characteristic-two identities for the exact arm
polynomials used by the connected-subtree row. -/
def characteristicTwoArmFormulas_claim39051 : Prop :=
  ∀ L : ℕ,
    ((1 + (Polynomial.X : F2Poly)) ^ 2 * armF L =
        Polynomial.C ((L % 2 : ℕ) : ZMod 2) * Polynomial.X +
          Polynomial.C (((L + 1) % 2 : ℕ) : ZMod 2) *
            Polynomial.X ^ 2 +
            Polynomial.X ^ (L + 2)) ∧
      ((1 + (Polynomial.X : F2Poly)) * armJ L =
        1 + Polynomial.X ^ (L + 1))

end

end MathlibPlus.Open.Combinatorics.R1540
