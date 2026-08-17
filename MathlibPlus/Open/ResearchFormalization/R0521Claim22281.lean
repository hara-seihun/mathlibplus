import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22281

open Filter Topology

noncomputable section

/-- Absence of finite accumulation for every time-slice of a bi-infinite train. -/
def noFiniteAccumulationAt (x : ℝ → ℤ → ℝ) : Prop :=
  ∀ (t a b : ℝ), {i : ℤ | a ≤ x t i ∧ x t i ≤ b}.Finite

/-- The zero-motion trajectory supplied by the preceding admitted claim. -/
def zeroMotionTrajectory (x : ℝ → ℤ → ℝ) : Prop :=
  (∀ t : ℝ, StrictMono (x t)) ∧
    noFiniteAccumulationAt x ∧
    ∀ (t : ℝ) (i : ℤ),
      HasDerivAt (fun s : ℝ => x s i)
        (2 * ∑' j : {j : ℤ // j ≠ i}, 1 / (x t i - x t j)) t

/-- The consecutive gap at time `t`. -/
def gapAt (x : ℝ → ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  x t (i + 1) - x t i

/-- The adjacent pressure at time `t`, with exactly the two adjacent indices
    omitted from its bi-infinite series. -/
noncomputable def adjacentPressureAt
    (x : ℝ → ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  2 - (gapAt x t i) ^ 2 *
    ∑' m : {m : ℤ // m ≠ i ∧ m ≠ i + 1},
      1 / ((x t (i + 1) - x t m) * (x t i - x t m))

/-- Claim 22281: zero motion gives the exact adjacent pressure and gap
    evolution identities. -/
def adjacentPressureAndGapEvolution_claim22281 : Prop :=
  ∀ (x : ℝ → ℤ → ℝ), zeroMotionTrajectory x →
    ∀ (t : ℝ) (i : ℤ),
      let d := gapAt x t i
      let P := adjacentPressureAt x t i
      HasDerivAt (fun s : ℝ => gapAt x s i) (2 * P / d) t ∧
        HasDerivAt (fun s : ℝ => (gapAt x s i) ^ 2) (4 * P) t

end

end MathlibPlus.Open.ResearchFormalization.R0521Claim22281
