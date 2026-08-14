import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open MeasureTheory

/-- The quarter-order jump magnitude in Claim 18106, with its value at the
single branch point chosen arbitrarily (which does not affect local
integrability). -/
noncomputable def quarterOrderJump (q u : ℝ) : ℝ :=
  Real.rpow |1 + q * u| (-1 / 4 : ℝ)

/-- Claim 18106: the jump is positive away from its branch point and locally
integrable across that point. -/
def quarterOrderBranchJumpPositiveAndLocallyIntegrable : Prop :=
  ∀ (q : ℝ),
    q ≠ 0 →
      (∀ u : ℝ, u ≠ -1 / q → 0 < quarterOrderJump q u) ∧
      (∀ ε : ℝ, 0 < ε →
        IntegrableOn
          (fun u : ℝ => quarterOrderJump q u)
          (Set.Ioo (-1 / q - ε) (-1 / q + ε)))

end MathlibPlus.Open.ResearchFormalization
