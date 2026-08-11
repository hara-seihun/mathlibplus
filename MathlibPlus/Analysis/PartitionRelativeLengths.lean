import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 40866: every finite increasing partition of `[X / 2, X]` has
    relative interval-length sum at least one half. -/
theorem partitionRelativeLengthsLowerBound
    (X : ℝ) (m : ℕ) (a : ℕ → ℝ)
    (hX : 0 < X) (hm : 0 < m)
    (ha0 : a 0 = X / 2) (ham : a m = X)
    (hainc : ∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ m → i < j → a i < a j) :
    (1 : ℝ) / 2 ≤
      ∑ i ∈ Finset.range m, (a (i + 1) - a i) / a (i + 1) := by
  have hterm : ∀ i ∈ Finset.range m,
      (a (i + 1) - a i) / X ≤ (a (i + 1) - a i) / a (i + 1) := by
    intro i hi
    have hi_lt : i < m := Finset.mem_range.mp hi
    have hi_succ_le : i + 1 ≤ m := Nat.succ_le_of_lt hi_lt
    have hdiff : 0 < a (i + 1) - a i := by
      have hlt := hainc (Nat.le_trans (Nat.le_succ i) hi_succ_le)
        hi_succ_le (Nat.lt_succ_self i)
      exact sub_pos.mpr hlt
    have ha0_pos : 0 < a 0 := by
      rw [ha0]
      linarith
    have ha_pos : 0 < a (i + 1) := by
      have hlt := hainc hm.le hi_succ_le (Nat.zero_lt_succ i)
      exact lt_trans ha0_pos hlt
    have ha_le : a (i + 1) ≤ X := by
      by_cases heq : i + 1 = m
      · rw [heq, ham]
      · have hlt : i + 1 < m := Nat.lt_of_le_of_ne hi_succ_le heq
        exact (hainc hi_succ_le (le_refl m) hlt).le.trans_eq ham
    apply (div_le_div_iff₀ hX ha_pos).2
    exact mul_le_mul_of_nonneg_left ha_le (le_of_lt hdiff)
  have hsum := Finset.sum_le_sum hterm
  calc
    (1 : ℝ) / 2 = (a m - a 0) / X := by
      rw [ham, ha0]
      field_simp
      norm_num
    _ = (∑ i ∈ Finset.range m, (a (i + 1) - a i)) / X := by
      rw [Finset.sum_range_sub]
    _ = ∑ i ∈ Finset.range m, (a (i + 1) - a i) / X := by
      rw [Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.range m, (a (i + 1) - a i) / a (i + 1) := hsum

end MathlibPlus.Analysis
