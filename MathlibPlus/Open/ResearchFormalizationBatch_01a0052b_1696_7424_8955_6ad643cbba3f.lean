import Mathlib

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a0052b_1696_7424_8955_6ad643cbba3f

noncomputable section

/-- The five-dimensional Newton staircase potential on positive radii. -/
def fiveDimensionalNewtonPotential (r : ℝ) : ℝ :=
  if 0 < r then Int.fract r / r ^ 3 else 0

/-- A smooth compactly supported radial test function on the positive half-line. -/
def radialTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ φ (Set.Ioi (0 : ℝ)) ∧
    HasCompactSupport (fun r : Set.Ioi (0 : ℝ) => φ r)

/-- Weak form of the flux derivative and shell-charge identity.

The coefficients `3` and `n` record, respectively, the value charge `3` and
 the action of the oriented dipole charge `-n` (since `δ'_n φ = -φ'(n)`). -/
def fluxDerivativeAndShellCharges : Prop :=
  ∀ φ : ℝ → ℝ,
    radialTestFunction φ →
      (∫ r in Set.Ioi (0 : ℝ),
          fiveDimensionalNewtonPotential r *
            derivWithin
              (fun s : ℝ => s ^ 4 * derivWithin φ (Set.Ioi (0 : ℝ)) s)
              (Set.Ioi (0 : ℝ)) r) =
        (-2 : ℝ) * (∫ r in Set.Ioi (0 : ℝ), φ r) +
          ∑' n : {n : ℕ // 1 ≤ n},
            (3 * φ (n : ℝ) +
              (n : ℝ) * derivWithin φ (Set.Ioi (0 : ℝ)) (n : ℝ))

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a0052b_1696_7424_8955_6ad643cbba3f
