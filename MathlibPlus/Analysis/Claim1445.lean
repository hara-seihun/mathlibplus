import Mathlib

namespace MathlibPlus.Analysis

/-- The logarithmic inequality used by claim 1445, with the positivity condition
made explicit as the domain condition for `log (h * T)`. -/
theorem log_mul_le_log_claim1445 {h T : ℝ}
    (hh : 0 < h) (hT : 0 < T) (hle : h ≤ 1) :
    Real.log (h * T) ≤ Real.log T := by
  rw [Real.log_mul (ne_of_gt hh) (ne_of_gt hT)]
  have hlog : Real.log h ≤ 0 := Real.log_nonpos hh.le hle
  linarith

end MathlibPlus.Analysis
