import Mathlib.Analysis.Real.Pi.Bounds

namespace MathlibPlus.Analysis.Claim53023

/-- Exact parameter and target-ray inequalities from admitted claim 53023.
The rational lower bound used for `π` is Mathlib's `3.14 < π`. -/
theorem parameter_certificate :
    let L : ℝ := 1529 / 10000
    let t : ℝ := 1479 / 10000
    let y : ℝ := 1 / 10
    let X : ℝ := 6000000185827
    let N : ℝ := 691164
    t + y ^ 2 / 2 = L ∧
      y ^ 2 < 1 - 2 * t ∧
      4 * Real.pi * (N ^ 2 - t / 16) > X + 1 ∧
      X + 1 > X + Real.sqrt (1 - y ^ 2) := by
  dsimp
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hsqrt : Real.sqrt ((1 : ℝ) - (1 / 10) ^ 2) < 1 := by
    have hnonneg : (0 : ℝ) ≤ 1 - (1 / 10) ^ 2 := by norm_num
    have hs := Real.sq_sqrt hnonneg
    have hroot : 0 ≤ Real.sqrt (1 - (1 / 10) ^ 2) := Real.sqrt_nonneg _
    nlinarith
  norm_num at hsqrt ⊢
  constructor
  · nlinarith [hpi]
  · nlinarith [hsqrt]

end MathlibPlus.Analysis.Claim53023
