import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/-- The rank-by-rank completion-cost sum in claim 47464.  This is the
arithmetic residue of the complete precedence schedule: rank `r` contributes
`r * (r - 1)`. -/
theorem completionCostSum_claim47464 (n : ℕ) :
    (∑ r ∈ Finset.range (n + 1), (r : ℚ) * ((r : ℚ) - 1)) =
      (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) - 1) / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      norm_num at ih ⊢
      rw [ih]
      ring

end MathlibPlus.Combinatorics
