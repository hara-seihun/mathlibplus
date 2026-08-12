import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

/-- Claim 49290: the finite weighted geometric sum.  The source range
`a = r, ..., r + h - 1` is represented by the zero-based index `j < h`,
with `a = r + j`; all displayed powers and sums are over `ℚ`. -/
theorem finiteWeightedGeometricSum (r h : ℕ) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.range h, (r + j : ℚ) / (2 : ℚ) ^ (r + j) =
      (((2 : ℚ) ^ h - 1) * (r + 1) - h) /
        (2 : ℚ) ^ (r + h - 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    have hrh : 1 ≤ r + h := by omega
    have hleft : r + h = (r + h - 1) + 1 := by omega
    have hright : r + (h + 1) - 1 = r + h := by omega
    rw [hright, hleft, pow_succ]
    push_cast
    field_simp
    ring

end MathlibPlus.Analysis
