import Mathlib

namespace MathlibPlus.Algebra.Claim8031

/-- The marginal gain of selecting the `(r + 1)`-st mode from a block of
multiplicity `m` is the corresponding odd step. Integer-valued parameters
make the displayed subtraction unambiguous. -/
theorem marginalGain (m r : ℤ) :
    (r + 1) * (m - (r + 1)) - r * (m - r) = m - 1 - 2 * r := by
  ring

end MathlibPlus.Algebra.Claim8031
