import MathlibPlus.Open.Combinatorics.R1540.Core

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

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
