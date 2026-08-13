import Mathlib

namespace MathlibPlus.Combinatorics.Claim47501

/-- Eight ternary positions have exactly `3^8` fillings. -/
theorem ternary_table_count_claim47501 :
    Fintype.card (Fin 8 → Fin 3) = 6561 := by
  simp

/-- The number of unordered pairs of those tables is the displayed census. -/
theorem ternary_pair_count_claim47501 :
    Nat.choose (Fintype.card (Fin 8 → Fin 3)) 2 = 21520080 := by
  rw [ternary_table_count_claim47501, Nat.choose_two_right]

end MathlibPlus.Combinatorics.Claim47501
