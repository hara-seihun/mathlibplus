import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a001bc_3fb0_71a5_8729_559cc8f5afca

/-- The five-dimensional Newton staircase on the positive radial half-line. -/
def fiveDimensionalNewtonStaircase (r : ℝ) : ℝ :=
  if 0 < r then Int.fract r / r ^ 3 else 0

/-- Exact Hermite quadrature identity for the Newton staircase. -/
def exactHermiteQuadratureIdentity : Prop :=
  ∀ (φ : ℝ → ℝ),
    ContDiff ℝ ⊤ φ →
    HasCompactSupport φ →
      (∫ r in Set.Ioi (0 : ℝ),
          fiveDimensionalNewtonStaircase r *
            deriv (fun x : ℝ => x ^ 4 * deriv φ x) r) =
        -2 * (∫ r in Set.Ioi (0 : ℝ), φ r) +
          ∑' n : ℕ,
            if 1 ≤ n then
              3 * φ (n : ℝ) + (n : ℝ) * deriv φ (n : ℝ)
            else 0

end MathlibPlus.Open.ResearchFormalizationBatch_01a001bc_3fb0_71a5_8729_559cc8f5afca
