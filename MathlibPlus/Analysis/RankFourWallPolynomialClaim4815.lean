import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic

namespace MathlibPlus.Analysis

/-- Claim 4815: the displayed rank-four wall polynomial in the source real
parameter context. -/
noncomputable def rankFourWallPolynomial_claim4815 : Polynomial ℝ :=
  4096 * Polynomial.X ^ 6 - 67584 * Polynomial.X ^ 5 +
    449280 * Polynomial.X ^ 4 - 1562880 * Polynomial.X ^ 3 +
    3049200 * Polynomial.X ^ 2 - 3243240 * Polynomial.X + 1486485

end MathlibPlus.Analysis
