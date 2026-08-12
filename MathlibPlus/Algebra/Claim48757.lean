import Mathlib

namespace MathlibPlus.Algebra.Claim48757

/-- The signed selector coefficients have unit total absolute mass on a
Rademacher value, as asserted in claim 48757. -/
theorem selector_abs_sum_claim48757 {X : ℝ}
    (hX : X = 1 ∨ X = -1) :
    |(1 - X) / 2| + |-(1 + X) / 2| = 1 := by
  rcases hX with rfl | rfl <;> norm_num

end MathlibPlus.Algebra.Claim48757
