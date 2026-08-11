import Mathlib

/-!
# Weighted principal-Lambert-W logarithm asymptotic

Registry node for admitted claim 495.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.Asymptotics

/-- The principal real Lambert-W branch has the stated log-log asymptotic and slow
variation, and its weighted logarithmic sum has the stated `n²` main term.

The branch is characterized only on the positive real axis, the only domain used here.
The finite sum is literally over `3 ≤ j ≤ n - 1`. -/
def weightedLambertWLogarithm : Prop :=
  ∃ W₀ : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → 0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) ∧
    (fun n : ℕ =>
        Real.log (W₀ (2 * (n : ℝ) / Real.exp 1)) -
          Real.log (Real.log (n : ℝ)))
      =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ c : ℝ, 0 < c →
      Tendsto
        (fun x : ℝ =>
          Real.log (W₀ (2 * (c * x) / Real.exp 1)) /
            Real.log (W₀ (2 * x / Real.exp 1)))
        atTop (𝓝 1)) ∧
    (fun n : ℕ =>
        2 * ∑ j ∈ Finset.Ico 3 n,
          ((n - j : ℕ) : ℝ) * Real.log (W₀ (2 * (j : ℝ) / Real.exp 1)) -
          (n : ℝ) ^ 2 * Real.log (Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

end MathlibPlus.Open.Asymptotics
