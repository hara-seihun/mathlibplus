import Mathlib

namespace MathlibPlus.Analysis.Claim13017

/-- The exact change-of-variables identity behind the corrected Lambert-W
inversion: with `z = 2 log (log x)`, one has
`(log x)^2 log (log x) = z exp z / 2`. -/
theorem lambertInversionFactorTwo_claim13017 (x : ℝ) (hx : 1 < x) :
    (Real.log x) ^ 2 * Real.log (Real.log x) =
      (2 * Real.log (Real.log x)) *
        Real.exp (2 * Real.log (Real.log x)) / 2 := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hexp : Real.exp (2 * Real.log (Real.log x)) =
      (Real.log x) ^ 2 := by
    rw [show 2 * Real.log (Real.log x) =
      Real.log (Real.log x) + Real.log (Real.log x) by ring,
      Real.exp_add, Real.exp_log hlog]
    ring
  rw [hexp]
  ring

end MathlibPlus.Analysis.Claim13017
