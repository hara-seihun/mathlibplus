import Mathlib

namespace MathlibPlus.Algebra.Claim17348

/-- The displayed boundary factor vanishes exactly on the two coordinate
hyperplanes; the gamma-ratio and boundary-carrier semantics remain explicit. -/
theorem boundary_matching_classification_claim17348 (a b : ℝ) :
    (a - 1) * (b - 1) = 0 ↔ a = 1 ∨ b = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> ring

end MathlibPlus.Algebra.Claim17348
