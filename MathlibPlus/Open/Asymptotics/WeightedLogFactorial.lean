import Mathlib

/-!
# Weighted logarithmic factorial asymptotic

Registry node for admitted claim 494.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.Asymptotics

/-- The weighted logarithmic sum has the stated `n²` main term and constant.
The finite sum is literally over `1 ≤ j ≤ n - 1`. -/
def weightedLogFactorial : Prop :=
  (fun n : ℕ =>
      2 * ∑ j ∈ Finset.Icc 1 (n - 1),
        ((n - j : ℕ) : ℝ) * Real.log (j : ℝ) -
        ((n : ℝ) ^ 2 * Real.log (n : ℝ) -
          (3 / 2 : ℝ) * (n : ℝ) ^ 2))
    =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

end MathlibPlus.Open.Asymptotics
