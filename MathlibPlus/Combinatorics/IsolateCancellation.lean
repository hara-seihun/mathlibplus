import Mathlib.Data.Nat.Choose.Basic

namespace MathlibPlus.Combinatorics.IsolateCancellation

/-- Claim 22849: the adjacent-layer isolate counts agree exactly. -/
theorem choose_isolate_cancellation_claim22849 (k j : ℕ) :
    Nat.choose k j * (k - j) = Nat.choose k (j + 1) * (j + 1) := by
  exact (Nat.choose_succ_right_eq k j).symm

end MathlibPlus.Combinatorics.IsolateCancellation
