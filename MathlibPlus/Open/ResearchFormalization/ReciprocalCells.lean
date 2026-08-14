import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The open reciprocal cell indexed by a positive natural number. -/
def reciprocalCell (n : ℕ) : Set ℝ :=
  Set.Ioo (1 / (n + 1 : ℝ)) (1 / (n : ℝ))

/-- Exact admitted claim 17798. -/
def reciprocalCellsPartitionVacuum : Prop :=
  (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ≠ n →
      Disjoint (reciprocalCell m) (reciprocalCell n)) ∧
    (⋃ n : {n : ℕ // 1 ≤ n}, reciprocalCell n.1) = Set.Ioo (0 : ℝ) 1 ∧
    (∀ n : ℕ, 1 ≤ n → (0 : ℝ) ∉ reciprocalCell n)

end MathlibPlus.Open.ResearchFormalization
