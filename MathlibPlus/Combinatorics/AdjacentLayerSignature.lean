import Mathlib

/-!
# Adjacent-layer exceptional signature

The first adjacent-layer vector in admitted claim 22853 has four nonzero
coordinates for every integer parameter `k ≥ 1`.
-/

namespace MathlibPlus.Combinatorics

/-- Every coordinate of the displayed first adjacent-layer signature is
nonzero in its stated integer range. -/
theorem adjacentLayerExceptionalVector_full (k : ℤ) (hk : 1 ≤ k) :
    (2 * k - 3 : ℤ) ≠ 0 ∧
      (-(2 * k - 1) : ℤ) ≠ 0 ∧
      (-(2 * k + 4) : ℤ) ≠ 0 ∧
      (2 * k + 6 : ℤ) ≠ 0 := by
  omega

end MathlibPlus.Combinatorics
