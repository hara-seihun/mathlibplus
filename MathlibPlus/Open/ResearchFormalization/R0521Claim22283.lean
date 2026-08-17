import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22283

noncomputable section

/-- The zero-motion and no-accumulation context for a bi-infinite zero train. -/
def noFiniteAccumulationAt (x : ℝ → ℤ → ℝ) : Prop :=
  ∀ (t a b : ℝ), {i : ℤ | a ≤ x t i ∧ x t i ≤ b}.Finite

def zeroMotionTrajectory (x : ℝ → ℤ → ℝ) : Prop :=
  (∀ t : ℝ, StrictMono (x t)) ∧
    noFiniteAccumulationAt x ∧
    ∀ (t : ℝ) (i : ℤ),
      HasDerivAt (fun s : ℝ => x s i)
        (2 * ∑' j : {j : ℤ // j ≠ i}, 1 / (x t i - x t j)) t

def gapAt (x : ℝ → ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  x t (i + 1) - x t i

noncomputable def adjacentPressureAt
    (x : ℝ → ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  2 - (gapAt x t i) ^ 2 *
    ∑' m : {m : ℤ // m ≠ i ∧ m ≠ i + 1},
      1 / ((x t (i + 1) - x t m) * (x t i - x t m))

/-- The finite normalized symmetric profile at time `t`. -/
noncomputable def normalizedProfileAt
    (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (1 / gapAt x t k) *
    ∑ j ∈ Finset.Icc 1 r,
      (gapAt x t (k - (j : ℤ)) +
        gapAt x t (k + (j : ℤ)) - 2 * gapAt x t k)

/-- The bracketed pressure-curvature expression in Claim 22283. -/
noncomputable def profilePressureCurvatureAt
    (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 r,
      (gapAt x t k * adjacentPressureAt x t (k - (j : ℤ)) /
          gapAt x t (k - (j : ℤ)) +
        gapAt x t k * adjacentPressureAt x t (k + (j : ℤ)) /
          gapAt x t (k + (j : ℤ)) -
        2 * adjacentPressureAt x t k)) -
    normalizedProfileAt x t k r * adjacentPressureAt x t k

/-- Claim 22283: direct differentiation of the normalized profile under the
    exact zero-motion gap and pressure evolution. -/
def exactProfileEvolutionIdentity_claim22283 : Prop :=
  ∀ (x : ℝ → ℤ → ℝ), zeroMotionTrajectory x →
    ∀ (t : ℝ) (k : ℤ) (r : ℕ), 1 ≤ r →
      HasDerivAt (fun s : ℝ => normalizedProfileAt x s k r)
        (2 / (gapAt x t k) ^ 2 * profilePressureCurvatureAt x t k r) t

end

end MathlibPlus.Open.ResearchFormalization.R0521Claim22283
