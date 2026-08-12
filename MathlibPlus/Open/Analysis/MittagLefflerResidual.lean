import Mathlib

/-!
# Positive Mittag–Leffler residual derivative

This registry node formalizes admitted claim 332. The positive integers in the
source series are indexed in Lean as `m + 1` with `m : ℕ`; no zero-frequency term
is introduced.
-/

open scoped Topology

namespace MathlibPlus.Open.Analysis

/-- The Bernoulli residual has the displayed Mittag–Leffler expansion; after the
change `t = 4u`, every contribution to `e` has positive logarithmic derivative
and the complete residual has positive derivative on `0 < u < log 2 / 2`. -/
def positiveMittagLefflerResidualDerivative : Prop :=
  let R : ℝ → ℝ := fun t =>
    t / (Real.exp t - 1) -
      (1 - t / 2 + t ^ 2 / 12 - t ^ 4 / 720)
  let summand : ℕ → ℝ → ℝ := fun m u =>
    Real.exp (-u) / 4 *
      (2 * (4 * u) ^ 6 /
        ((2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 4 *
          ((2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 + (4 * u) ^ 2)))
  let e : ℝ → ℝ := fun u => Real.exp (-u) * R (4 * u) / 4
  (∀ t : ℝ, 0 < t →
    R t = 2 * t ^ 6 * ∑' m : ℕ,
      1 / ((2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 4 *
        ((2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 + t ^ 2))) ∧
  (∀ (m : ℕ) (u : ℝ), 0 < u → u < Real.log 2 / 2 →
    0 < deriv (fun v => Real.log (summand m v)) u) ∧
  ∀ u : ℝ, 0 < u → u < Real.log 2 / 2 → 0 < deriv e u

end MathlibPlus.Open.Analysis
