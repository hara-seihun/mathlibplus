-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.NumberTheory

/-- The exact prime product through 100 exceeds `0.4298`. -/
theorem primeProduct_le_100_gt_4298 :
    (∏ p ∈ (Finset.filter Nat.Prime (Finset.Icc 2 100)),
      (1 - 2 / (p : ℚ)^2 + 1 / (p : ℚ)^3)) > (4298 : ℚ) / 10000 := by
  native_decide

end MathlibPlus.NumberTheory
