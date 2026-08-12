import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim20458

/-- The four outside-cell counts displayed in claim 20458.  Integer-valued
counts preserve the literal affine formula without silently choosing truncated
natural subtraction; the source graph/profile carrier is not reconstructed. -/
def fourCellCounts (n d e c epsilon : ℤ) : Fin 4 → ℤ :=
  ![c, d - epsilon - c, e - epsilon - c,
    n - 2 - d - e + 2 * epsilon + c]

theorem fourCellCounts_entries_claim20458
    (n d e c epsilon : ℤ) :
    fourCellCounts n d e c epsilon 0 = c ∧
      fourCellCounts n d e c epsilon 1 = d - epsilon - c ∧
      fourCellCounts n d e c epsilon 2 = e - epsilon - c ∧
      fourCellCounts n d e c epsilon 3 =
        n - 2 - d - e + 2 * epsilon + c := by
  simp [fourCellCounts]

theorem fourCellCounts_total_claim20458
    (n d e c epsilon : ℤ) :
    ∑ i : Fin 4, fourCellCounts n d e c epsilon i = n - 2 := by
  simp [fourCellCounts, Fin.sum_univ_succ]
  ring

end MathlibPlus.Combinatorics.Claim20458
