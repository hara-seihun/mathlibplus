import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim12025

def repeatedPositiveZeroCounterfeit_claim12025 : Prop :=
  let E : Polynomial ℂ :=
    (1 + Polynomial.X) ^ 2 * (1 + Polynomial.X ^ 2)
  E = 1 + 2 * Polynomial.X + 2 * Polynomial.X ^ 2 +
        2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 ∧
    E = (1 + Polynomial.X) ^ 2 *
      (Polynomial.X - Polynomial.C Complex.I) *
      (Polynomial.X + Polynomial.C Complex.I)

end MathlibPlus.Open.Analysis.Claim12025

end
