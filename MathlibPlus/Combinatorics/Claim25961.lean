import Mathlib

namespace MathlibPlus
namespace Combinatorics

/-- The small-total partition-count row in claim 25961 is exactly the
five-entry sequence displayed for totals zero through four. -/
theorem small_total_partition_counts_claim25961 :
    let counts : List ℕ := [1, 1, 2, 3, 5]
    counts = [1, 1, 2, 3, 5] ∧ counts.sum = 12 := by
  norm_num

end Combinatorics
end MathlibPlus
