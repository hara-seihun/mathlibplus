import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

open BigOperators

/-- Claim 16760: distinct nonempty prefix sums are equivalent to the absence of
zero consecutive blocks after the first entry; including the empty prefix adds
exactly the zero-initial-block cases. -/
theorem consecutiveZeroBlockEquivalence_claim16760
    {G : Type*} [AddCommGroup G]
    (a : ℕ → G) (t : ℕ) :
    let prefixSum := fun n : ℕ => ∑ k ∈ Finset.range n, a k
    let blockSum := fun (i j : ℕ) => ∑ k ∈ Finset.Ico i j, a k
    ((∀ i ∈ Finset.range (t + 1), 0 < i →
        ∀ j ∈ Finset.range (t + 1), 0 < j → i ≠ j →
          prefixSum i ≠ prefixSum j) ↔
      (∀ i j, 1 ≤ i → i < j → j ≤ t → blockSum i j ≠ 0)) ∧
    ((∀ i ∈ Finset.range (t + 1),
        ∀ j ∈ Finset.range (t + 1), i ≠ j →
          prefixSum i ≠ prefixSum j) ↔
      (∀ i j, i < j → j ≤ t → blockSum i j ≠ 0)) := by
  dsimp
  constructor
  · constructor
    · intro hp i j hi hij hj hzero
      have hle : i ≤ j := hij.le
      have hsum : (∑ k ∈ Finset.range j, a k) - ∑ k ∈ Finset.range i, a k = 0 := by
        rw [← Finset.sum_Ico_eq_sub a hle]
        exact hzero
      have heq : (∑ k ∈ Finset.range j, a k) = ∑ k ∈ Finset.range i, a k :=
        sub_eq_zero.mp hsum
      have hi_mem : i ∈ Finset.range (t + 1) := by
        apply Finset.mem_range.mpr
        omega
      have hj_mem : j ∈ Finset.range (t + 1) := by
        apply Finset.mem_range.mpr
        omega
      exact (hp i hi_mem (by omega) j hj_mem (by omega) (ne_of_lt hij)) heq.symm
    · intro hn i hi_mem hi_pos j hj_mem hj_pos hne heq
      have hi_lt : i < t + 1 := Finset.mem_range.mp hi_mem
      have hj_lt : j < t + 1 := Finset.mem_range.mp hj_mem
      rcases lt_or_gt_of_ne hne with hij | hji
      · apply hn i j (by omega) hij (by omega)
        rw [Finset.sum_Ico_eq_sub a hij.le]
        exact sub_eq_zero.mpr heq.symm
      · apply hn j i (by omega) hji (by omega)
        rw [Finset.sum_Ico_eq_sub a hji.le]
        exact sub_eq_zero.mpr heq
  · constructor
    · intro hp i j hij hj hzero
      have hle : i ≤ j := hij.le
      have hsum : (∑ k ∈ Finset.range j, a k) - ∑ k ∈ Finset.range i, a k = 0 := by
        rw [← Finset.sum_Ico_eq_sub a hle]
        exact hzero
      have heq : (∑ k ∈ Finset.range j, a k) = ∑ k ∈ Finset.range i, a k :=
        sub_eq_zero.mp hsum
      have hi_mem : i ∈ Finset.range (t + 1) := by
        apply Finset.mem_range.mpr
        omega
      have hj_mem : j ∈ Finset.range (t + 1) := by
        apply Finset.mem_range.mpr
        omega
      exact (hp i hi_mem j hj_mem (ne_of_lt hij)) heq.symm
    · intro hn i hi_mem j hj_mem hne heq
      have hi_lt : i < t + 1 := Finset.mem_range.mp hi_mem
      have hj_lt : j < t + 1 := Finset.mem_range.mp hj_mem
      rcases lt_or_gt_of_ne hne with hij | hji
      · apply hn i j hij (by omega)
        rw [Finset.sum_Ico_eq_sub a hij.le]
        exact sub_eq_zero.mpr heq.symm
      · apply hn j i hji (by omega)
        rw [Finset.sum_Ico_eq_sub a hji.le]
        exact sub_eq_zero.mpr heq

end MathlibPlus.Combinatorics
