import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The even-monomial theta coordinate sequence from the source packet. -/
noncomputable def evenMonomialThetaCoordinate_claim18280 (n : ℕ) (t : ℝ) : ℝ :=
  2 * t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

end MathlibPlus.Analysis
