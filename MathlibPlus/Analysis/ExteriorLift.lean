import Mathlib

namespace MathlibPlus.Analysis.ExteriorLift

/-- The exterior lift `T ↦ (T + √(T²-4))/2` is strictly increasing on
`(2,∞)`. -/
theorem strictMono_exteriorLift_claim4521 :
    StrictMonoOn
      (fun T : ℝ => (T + Real.sqrt (T ^ 2 - 4)) / 2)
      (Set.Ioi 2) := by
  intro x hx y hy hxy
  change 2 < x at hx
  change 2 < y at hy
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hsq : x ^ 2 - 4 < y ^ 2 - 4 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hxpos hypos)]
  have hnonnegx : 0 ≤ x ^ 2 - 4 := by nlinarith [hx]
  have hnonnegy : 0 ≤ y ^ 2 - 4 := by nlinarith [hy]
  have hsqrt : Real.sqrt (x ^ 2 - 4) < Real.sqrt (y ^ 2 - 4) := by
    nlinarith [Real.sq_sqrt hnonnegx, Real.sq_sqrt hnonnegy,
      Real.sqrt_nonneg (x ^ 2 - 4), Real.sqrt_nonneg (y ^ 2 - 4)]
  linarith

end MathlibPlus.Analysis.ExteriorLift
