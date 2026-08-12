import Mathlib

namespace MathlibPlus.Algebra.Claim4819

noncomputable section

/-- The explicit rank-three wall polynomial from claim 4819. -/
def rankThreeWallPolynomial : Polynomial ℚ :=
  64 * Polynomial.X ^ 3 - 432 * Polynomial.X ^ 2 +
    924 * Polynomial.X - 693

theorem rankThreeWallPolynomial_eval (q : ℚ) :
    rankThreeWallPolynomial.eval q =
      64 * q ^ 3 - 432 * q ^ 2 + 924 * q - 693 := by
  simp [rankThreeWallPolynomial]

end

end MathlibPlus.Algebra.Claim4819
