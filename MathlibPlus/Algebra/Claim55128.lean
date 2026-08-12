import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim55128

/-- The free-seam decomposition in claim 55128, interpreted in an arbitrary
`ℚ`-module. -/
theorem seamLinearDecomposition {V : Type*} [AddCommGroup V] [Module ℚ V]
    (w : ℚ) (s t : V) :
    w • s + w • t = (s + (2 * w - 1) • t) + (w - 1) • (s - t) := by
  module

/-- The layer weights in claim 55128 have the displayed affine sum. -/
theorem layerWeightIdentity (k : ℕ) :
    (2 * (k : ℚ) + 3 / 2) + 2 * ((k : ℚ) + 1 / 4) =
      4 * (k : ℚ) + 2 := by
  ring

/-- Summing the layer weights for `k < i` gives the displayed quadratic. -/
theorem layerWeightSum (i : ℕ) :
    (∑ k ∈ Finset.range i,
      ((2 * (k : ℚ) + 3 / 2) + 2 * ((k : ℚ) + 1 / 4))) =
      2 * (i : ℚ) ^ 2 := by
  induction i with
  | zero => norm_num
  | succ i ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

end MathlibPlus.Algebra.Claim55128
