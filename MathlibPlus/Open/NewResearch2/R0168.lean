import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0168

open scoped BigOperators
open scoped Topology

/-- Claim 18502: the canonical theta shell is the ground shell plus its
nonnegative tail, with the displayed affine interpolation on the unit interval. -/
def claim18502_groundShellTailInterpolation : Prop :=
  let lambda : ℝ := Real.pi
  let thetaShell : ℕ → ℝ → ℝ := fun n u =>
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let a : ℝ → ℝ := fun u => thetaShell 1 u
  let b : ℝ → ℝ := fun u => ∑' n : ℕ, thetaShell (n + 2) u
  let t : ℝ → ℝ → ℝ := fun q u => a u + q * b u
  let full : ℝ → ℝ := fun u => ∑' n : ℕ, thetaShell (n + 1) u
  lambda = Real.pi ∧
    (∀ q : ℝ, q ∈ Set.Icc 0 1 → t q = fun u => a u + q * b u) ∧
    t 0 = a ∧ t 1 = full

end MathlibPlus.Open.NewResearch2.R0168
