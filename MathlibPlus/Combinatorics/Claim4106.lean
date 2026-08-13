import Mathlib

namespace MathlibPlus.Combinatorics.Claim4106

/-- The two displayed three-column rows differ already in the first column. -/
theorem row_witness_ne_claim4106 :
    (![2, 6, 2] : Fin 3 → ℕ) ≠ ![9, 36, 16] := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0

end MathlibPlus.Combinatorics.Claim4106
