import Mathlib

namespace MathlibPlus.Algebra

/-- A positive height has a nonnegative free reserve exactly when its coefficient is at least two. -/
theorem nonnegativeFreeReserve_iff_claim18278 {c i : ℝ} (hi : 0 < i) :
    0 ≤ (c - 2) * i ^ 2 ↔ c ≥ 2 := by
  have hi2 : 0 < i ^ 2 := sq_pos_of_pos hi
  constructor
  · intro h
    have hc : 0 ≤ c - 2 := (mul_nonneg_iff_of_pos_right hi2).mp h
    linarith
  · intro hc
    exact (mul_nonneg_iff_of_pos_right hi2).mpr (by linarith)

end MathlibPlus.Algebra
