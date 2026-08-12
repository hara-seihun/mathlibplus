import Mathlib

namespace MathlibPlus.Analysis.CholeskyFreeBlock

/-- The exact logarithmic pivot-defect identity from admitted claim 8533.
On a free block, `r = sqrt q`, `s = c / sqrt q`, and
`δ = q / c - 1`; the ratio is therefore `1 + δ`. -/
theorem logPivotDefect_claim8533
    (c q : ℝ) (hc : 0 < c) (hq : 0 < q) :
    let r := Real.sqrt q
    let s := c / Real.sqrt q
    let δ := q / c - 1
    Real.log (r / s) = Real.log (1 + δ) := by
  dsimp
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  have hratio : Real.sqrt q / (c / Real.sqrt q) = q / c := by
    field_simp [ne_of_gt hc, ne_of_gt hsqrt]
    nlinarith
  rw [hratio]
  congr 1
  field_simp [ne_of_gt hc]
  ring

end MathlibPlus.Analysis.CholeskyFreeBlock
