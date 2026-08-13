import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The finite-index formalization of the one-hole contour term. The product
runs over every index other than `j`; the exponent condition is the source's
`n = r-k+1 ≥ 1`, and the final equality records the geometric ratio. -/
def scalarOneHoleContourAction_claim8130 : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (M y : ℝ) (x c : ι → ℝ) (k r : ℕ),
    k ≤ r →
    0 ≤ M →
    c j ≠ 0 →
    0 < y / x j →
    y / x j < 1 →
    let B : ℕ → ℝ := fun r =>
      M / |c j| * (y / x j) ^ (r - k + 1) *
        ∏ i : ι, if i = j then 1 else ((x i + y) / |x i - x j|) ^ 2
    0 ≤ B r ∧
      B (r + 1) = (y / x j) * B r ∧
      B (r + 1) ≤ B r

end MathlibPlus.Open.Analysis
