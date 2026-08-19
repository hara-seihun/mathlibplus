import MathlibPlus.Open.NewResearch2.Q0002_Factorial15715

namespace MathlibPlus.Algebra.R0301

open MathlibPlus.Open.NewResearch2.Q0002.Factorial15715

/-- Claim 19552: the canonical source rank-two polynomial, after the cup
shift `X ↦ c+X`, has the exact constant and linear coefficients. -/
def exactShiftedRankTwoCoefficients_claim19552 : Prop :=
  ∀ c : ℝ,
    (g1Polynomial.comp (Polynomial.X + Polynomial.C c)).coeff 0 =
        2 * c - 7 / 2 ∧
      (g1Polynomial.comp (Polynomial.X + Polynomial.C c)).coeff 1 = 2

end MathlibPlus.Algebra.R0301
