import Mathlib

namespace MathlibPlus.NumberTheory

/--
The divisibility premise excluded in Claim 28192's ternary inner-holomorph
route, with the displayed orders retained literally.
-/
theorem claim28192_innerHolomorphDivisibilityFails :
    ¬ (8 : ℕ) ∣ (5 - 1 : ℕ) := by
  norm_num

end MathlibPlus.NumberTheory
