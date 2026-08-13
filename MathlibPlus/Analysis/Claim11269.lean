import Mathlib

namespace MathlibPlus.Analysis.Claim11269

/-- The square-coordinate substitution from claim 11269: after putting
`s = i t`, the coordinate `s^2` is `-t^2`.  The real parameter is coerced
into `ℂ`, which makes the packet's shorthand `x ↦ -x` literal. -/
theorem squareCoordinateSubstitution_claim11269 (t : ℝ) :
    (((Complex.I : ℂ) * (t : ℂ)) ^ 2) = -((t : ℂ) ^ 2) := by
  rw [mul_pow, Complex.I_sq]
  ring

end MathlibPlus.Analysis.Claim11269
