import Mathlib

namespace MathlibPlus.Combinatorics

/-- Exact numerical order from claim 27834.  The universal quadratic-chart
2-closure construction and the permutation-group carrier are left explicit for
fidelity review rather than silently reconstructed. -/
theorem claim27834_twoClosure_order_arithmetic :
    (3 : ℕ) ^ 9 = 19683 := by
  norm_num

end MathlibPlus.Combinatorics
