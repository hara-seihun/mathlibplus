import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim5341

/-- The four symmetric-power dimensions in the edge-seventeen kernel add to 35. -/
theorem edge_seventeen_dimension_claim5341 :
    Nat.choose 6 4 + Nat.choose 5 3 + Nat.choose 5 4 + Nat.choose 5 4 = (35 : ℕ) := by
  norm_num [Nat.choose]

/-- The reported bulk rank leaves a 35-dimensional defect. -/
theorem edge_seventeen_rank_defect_claim5341 :
    12870 - 12835 = (35 : ℕ) := by norm_num

end MathlibPlus.LinearAlgebra.Claim5341
