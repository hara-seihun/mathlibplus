import Mathlib

namespace MathlibPlus.Analysis.Claim52029

/-- Exact first-query totals and the minimizing `Y₂` entry from claim 52029.
The Bellman-recursion carrier is not reconstructed from the packet. -/
theorem unrestricted_query_totals_claim52029 :
    let totals : Fin 3 → ℚ := ![20117 / 12482, 9815 / 6241, 6892 / 6241]
    let A : ℚ := 6892 / 6241
    totals 0 = 20117 / 12482 ∧
      totals 1 = 9815 / 6241 ∧
      totals 2 = 6892 / 6241 ∧
      (∀ i : Fin 3, totals 2 ≤ totals i) ∧
      A = totals 2 ∧ A < 2 := by
  dsimp
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro i
    fin_cases i <;> norm_num
  constructor
  · rfl
  · norm_num

end MathlibPlus.Analysis.Claim52029
