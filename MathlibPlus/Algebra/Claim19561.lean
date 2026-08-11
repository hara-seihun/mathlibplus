import Mathlib

namespace MathlibPlus.Algebra.Claim19561

/-- The displayed one-tooth defect factors without changing the two signed
terms. -/
theorem oneToothDefect_factorization (w S T : ℝ) :
    (w - 1) * S - (w - 1) * T = (w - 1) * (S - T) := by
  ring

end MathlibPlus.Algebra.Claim19561
