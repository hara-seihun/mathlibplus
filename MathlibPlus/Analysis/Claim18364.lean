import Mathlib

namespace MathlibPlus.Analysis.Claim18364

/-- Complementation about the centered logarithmic coordinate is reflection.
The source's divisor-pair carrier is represented by `de = R / d`. -/
theorem centered_complement_reflection_claim18364
    (R d de : ℝ) (hR : 0 < R) (hd : 0 < d) (hde : de = R / d) :
    (Real.log de - (1 / 2 : ℝ) * Real.log R) =
      -(Real.log d - (1 / 2 : ℝ) * Real.log R) := by
  rw [hde, Real.log_div (ne_of_gt hR) (ne_of_gt hd)]
  ring

end MathlibPlus.Analysis.Claim18364
