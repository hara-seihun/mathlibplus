import Mathlib

namespace MathlibPlus.Analysis.EigenvalueBands

/-- Distinct positive integer cells have disjoint open real-square bands. -/
theorem distinctIntegerCells_disjoint
    {n m : ℕ} (_hn : 0 < n) (_hm : 0 < m) (hneq : n ≠ m) :
    Disjoint
      (Set.Ioo ((n : ℝ) ^ 2) (((n + 1 : ℕ) : ℝ) ^ 2))
      (Set.Ioo ((m : ℝ) ^ 2) (((m + 1 : ℕ) : ℝ) ^ 2)) := by
  have hforward : ∀ {a b : ℕ}, a < b →
      Disjoint
        (Set.Ioo ((a : ℝ) ^ 2) (((a + 1 : ℕ) : ℝ) ^ 2))
        (Set.Ioo ((b : ℝ) ^ 2) (((b + 1 : ℕ) : ℝ) ^ 2)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hx hy
    have hsucc : a + 1 ≤ b := Nat.succ_le_of_lt hab
    have hcast : ((a + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hsucc
    have ha_nonneg : 0 ≤ ((a + 1 : ℕ) : ℝ) := by positivity
    have hb_nonneg : 0 ≤ (b : ℝ) := by positivity
    have hsquares : ((a + 1 : ℕ) : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by
      nlinarith
    linarith [hx.2, hy.1]
  rcases Nat.lt_or_gt_of_ne hneq with hnm | hmn
  · exact hforward hnm
  · exact (hforward hmn).symm

end MathlibPlus.Analysis.EigenvalueBands
