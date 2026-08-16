import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.Analysis

/--
The normalized all-order multiplier has the stated linear-frequency
limit, derivative, and strict negativity of its limiting rate.
-/
def linearFrequencyAction : Prop :=
  let W : ℕ → ℝ → ℝ := fun m τ =>
    Real.exp (2 * (m : ℝ)) /
        ((8 : ℝ) * (m : ℝ) ^ (2 * m + 2) *
          Real.cosh (Real.pi * τ / 2)) *
      Finset.prod (Finset.Icc 1 m)
        (fun j => ((j : ℝ) ^ 2 + τ ^ 2 / 4))
  let linearFrequencyRate : ℝ → ℝ := fun y =>
    Real.log (1 + y ^ 2) - 2 * |y| * Real.arctan |y|
  (∀ y : ℝ,
      Filter.Tendsto
        (fun m : ℕ =>
          (1 / (m : ℝ)) * Real.log (W m (2 * (m : ℝ) * y)))
        atTop
        (𝓝 (Real.log (1 + y ^ 2) - 2 * |y| * Real.arctan |y|))) ∧
    (∀ y : ℝ,
      0 < y →
        HasDerivAt linearFrequencyRate (-2 * Real.arctan y) y ∧
          -2 * Real.arctan y < 0) ∧
    (∀ y : ℝ, y ≠ 0 → linearFrequencyRate y < 0)

end MathlibPlus.Open.Analysis
