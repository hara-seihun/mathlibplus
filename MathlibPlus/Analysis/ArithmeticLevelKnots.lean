import Mathlib

namespace MathlibPlus.Analysis.ArithmeticLevelKnots

/--
Claim 17691.  For a positive arithmetic level `m`, with the level and its
logarithmic coordinate inlined as `π m²` and `log (π m²)`, the knot coordinate
has the displayed additive form.  The positivity restriction is the domain
needed by the logarithm of the integer level.
-/
theorem arithmeticLevelLogKnot (m : ℕ) (hm : 0 < m) :
    Real.log (Real.pi * (m : ℝ) ^ 2) =
      Real.log Real.pi + 2 * Real.log (m : ℝ) := by
  rw [Real.log_mul (ne_of_gt Real.pi_pos) (by positivity)]
  rw [Real.log_pow]
  ring

end MathlibPlus.Analysis.ArithmeticLevelKnots
