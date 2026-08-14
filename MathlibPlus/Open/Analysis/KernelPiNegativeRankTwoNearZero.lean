import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The kernel from the admitted near-zero ordered-minor claim. -/
noncomputable def kernelPiNegativeRankTwoNearZeroK (x u : ℝ) : ℝ :=
  x *
    (Real.exp
        (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
      Real.exp
        (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

/-- The ordered rank-two minor is negative for sufficiently small positive `u`. -/
def kernelPiNegativeRankTwoNearZero : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
      ∀ u : ℝ,
        0 < u →
          u < ε →
            kernelPiNegativeRankTwoNearZeroK (1 / 10 : ℝ) 0 *
                  kernelPiNegativeRankTwoNearZeroK 1 u -
                kernelPiNegativeRankTwoNearZeroK (1 / 10 : ℝ) u *
                  kernelPiNegativeRankTwoNearZeroK 1 0 <
              0

end MathlibPlus.Open.Analysis
