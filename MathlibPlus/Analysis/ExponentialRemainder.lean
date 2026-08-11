import Mathlib

/-!
# Exponential remainder

Formalization of admitted claim 18437.
-/

namespace MathlibPlus.Analysis.ExponentialRemainder

/-- The exponential remainder `exp (2u) - 1 - 2u` is nonnegative at every real `u`. -/
theorem nonnegativity (u : ℝ) :
    0 ≤ Real.exp (2 * u) - 1 - 2 * u := by
  have h := Real.add_one_le_exp (2 * u)
  linarith

end MathlibPlus.Analysis.ExponentialRemainder
