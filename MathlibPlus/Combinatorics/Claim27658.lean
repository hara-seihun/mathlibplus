import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim27658

noncomputable section

private def armIntervalCount (arm size : ℕ) : ℤ :=
  if size ≤ arm then ((arm - size + 1 : ℕ) : ℤ) else 0

private def centerContainingCount
    (α β γ target : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (α + 1),
    (((Finset.range (β + 1)).filter
      (fun j => i + j ≤ target ∧ target - (i + j) ≤ γ)).card : ℤ)

private def centerContainingCountSimple
    (α β target : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (α + 1),
    (((Finset.range (β + 1)).filter
      (fun j => i + j ≤ target)).card : ℤ)

private def spiderConnectedSetCount
    (α β γ size : ℕ) : ℤ :=
  armIntervalCount α size
    + armIntervalCount β size
    + armIntervalCount γ size
    + centerContainingCount α β γ (size - 1)

theorem spiderMidpointConnectedCountDifference_claim27658
    {a b : ℕ} (a_pos : 1 ≤ a) (a_lt_b : a < b) :
    (armIntervalCount a (a + 3)
          + armIntervalCount b (a + 3)
          + armIntervalCount (a + b) (a + 3))
        - (armIntervalCount a (a + 3)
          + armIntervalCount a (a + 3)
          + armIntervalCount (2 * b) (a + 3)) =
        (if b = a + 1 then -1 else -2) ∧
      centerContainingCount a b (a + b) (a + 2)
        - centerContainingCount a a (2 * b) (a + 2) =
        (if b = a + 1 then 2 else 3) ∧
      spiderConnectedSetCount a b (a + b) (a + 3)
        - spiderConnectedSetCount a a (2 * b) (a + 3) = 1 := by
  have centerContainingCount_eq_simple
      {α β γ target : ℕ} (target_le_gamma : target ≤ γ) :
      centerContainingCount α β γ target =
        centerContainingCountSimple α β target := by
    classical
    unfold centerContainingCount centerContainingCountSimple
    apply Finset.sum_congr rfl
    intro i i_mem
    have filter_eq :
        (Finset.range (β + 1)).filter
            (fun j => i + j ≤ target ∧ target - (i + j) ≤ γ) =
          (Finset.range (β + 1)).filter (fun j => i + j ≤ target) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨j_mem, sum_le, remainder_le⟩
        exact ⟨j_mem, sum_le⟩
      · rintro ⟨j_mem, sum_le⟩
        exact ⟨j_mem, sum_le, by omega⟩
    rw [filter_eq]
  have centerContainingCountSimple_succ
      (α β target : ℕ) :
      centerContainingCountSimple α (β + 1) target =
        centerContainingCountSimple α β target
          + (∑ i ∈ Finset.range (α + 1),
              (if i + (β + 1) ≤ target then (1 : ℤ) else 0)) := by
    classical
    unfold centerContainingCountSimple
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i i_mem
    have range_eq :
        Finset.range (β + 1 + 1) =
          insert (β + 1) (Finset.range (β + 1)) := by
      rw [Finset.range_add_one]
    rw [range_eq, Finset.filter_insert]
    by_cases h : i + (β + 1) ≤ target
    · simp [h]
    · simp [h]
  have centerContainingCountSimple_eq_of_target_le_bound
      {α β target : ℕ} (target_le_bound : target ≤ β) :
      centerContainingCountSimple α β target =
        centerContainingCountSimple α target target := by
    classical
    unfold centerContainingCountSimple
    apply Finset.sum_congr rfl
    intro i i_mem
    have filter_eq :
        (Finset.range (β + 1)).filter (fun j => i + j ≤ target) =
          (Finset.range (target + 1)).filter (fun j => i + j ≤ target) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [filter_eq]
  have indicator_sum_two
      (a : ℕ) (a_pos : 1 ≤ a) :
      (∑ i ∈ Finset.range (a + 1),
        (if i + (a + 1) ≤ a + 2 then (1 : ℤ) else 0)) = 2 := by
    classical
    have condition (i : ℕ) :
        i + (a + 1) ≤ a + 2 ↔ i ≤ 1 := by omega
    simp_rw [condition]
    have filter_eq :
        (Finset.range (a + 1)).filter (fun i => i ≤ 1) =
          Finset.range 2 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter, filter_eq]
    simp
  have indicator_sum_one (a : ℕ) :
      (∑ i ∈ Finset.range (a + 1),
        (if i + (a + 2) ≤ a + 2 then (1 : ℤ) else 0)) = 1 := by
    classical
    have condition (i : ℕ) :
        i + (a + 2) ≤ a + 2 ↔ i = 0 := by omega
    simp_rw [condition]
    have filter_eq :
        (Finset.range (a + 1)).filter (fun i => i = 0) =
          ({0} : Finset ℕ) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [← Finset.sum_filter, filter_eq]
    simp
  have center_midpoint_difference
      {a b : ℕ} (a_pos : 1 ≤ a) (a_lt_b : a < b) :
      centerContainingCount a b (a + b) (a + 2)
        - centerContainingCount a a (2 * b) (a + 2) =
          if b = a + 1 then 2 else 3 := by
    have target_le_middle : a + 2 ≤ a + b := by omega
    have target_le_left : a + 2 ≤ 2 * b := by omega
    rw [centerContainingCount_eq_simple target_le_middle,
      centerContainingCount_eq_simple target_le_left]
    by_cases adjacent : b = a + 1
    · subst b
      rw [centerContainingCountSimple_succ]
      rw [indicator_sum_two a a_pos]
      simp
    · have bound : a + 2 ≤ b := by omega
      rw [centerContainingCountSimple_eq_of_target_le_bound bound]
      rw [centerContainingCountSimple_succ]
      rw [centerContainingCountSimple_succ]
      rw [indicator_sum_two a a_pos, indicator_sum_one a]
      ring_nf
      have not_adjacent' : ¬b = 1 + a := by omega
      simp [not_adjacent']
  have arm_midpoint_difference
      {a b : ℕ} (a_pos : 1 ≤ a) (a_lt_b : a < b) :
      (armIntervalCount a (a + 3)
          + armIntervalCount b (a + 3)
          + armIntervalCount (a + b) (a + 3))
        - (armIntervalCount a (a + 3)
          + armIntervalCount a (a + 3)
          + armIntervalCount (2 * b) (a + 3)) =
          if b = a + 1 then -1 else -2 := by
    by_cases adjacent : b = a + 1
    · subst b
      simp only [armIntervalCount]
      split_ifs <;> omega
    · have bound : a + 2 ≤ b := by omega
      simp only [armIntervalCount]
      split_ifs <;> omega
  have center_difference := center_midpoint_difference a_pos a_lt_b
  have arm_difference := arm_midpoint_difference a_pos a_lt_b
  refine ⟨arm_difference, center_difference, ?_⟩
  have size_sub : a + 3 - 1 = a + 2 := by omega
  unfold spiderConnectedSetCount
  rw [size_sub]
  calc
    armIntervalCount a (a + 3) + armIntervalCount b (a + 3)
          + armIntervalCount (a + b) (a + 3)
          + centerContainingCount a b (a + b) (a + 2) -
        (armIntervalCount a (a + 3) + armIntervalCount a (a + 3)
          + armIntervalCount (2 * b) (a + 3)
          + centerContainingCount a a (2 * b) (a + 2)) =
      (armIntervalCount a (a + 3) + armIntervalCount b (a + 3)
          + armIntervalCount (a + b) (a + 3) -
        (armIntervalCount a (a + 3) + armIntervalCount a (a + 3)
          + armIntervalCount (2 * b) (a + 3))) +
        (centerContainingCount a b (a + b) (a + 2) -
          centerContainingCount a a (2 * b) (a + 2)) := by ring
    _ = 1 := by
      rw [arm_difference, center_difference]
      split_ifs <;> omega

end

end MathlibPlus.Combinatorics.Claim27658
