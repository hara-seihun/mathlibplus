import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.NumberTheory

private lemma sum_inv_two_pow_shift_claim16205 (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 / (2 : ℚ)) ^ (j + 1) =
      1 - (1 / (2 : ℚ)) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private lemma sum_j_inv_two_pow_shift_claim16205 (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℚ) * (1 / (2 : ℚ)) ^ (j + 1) =
      2 - (m + 2 : ℚ) * (1 / (2 : ℚ)) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

private lemma pow_two_ge_strong_claim16205 (m : ℕ) (hm : 1 ≤ m) :
    m + 3 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        norm_num
      · have hm' : 1 ≤ m := by omega
        calc
          m + 1 + 3 ≤ 2 * (m + 3) := by omega
          _ ≤ 2 * 2 ^ (m + 1) := Nat.mul_le_mul_left 2 (ih hm')
          _ = 2 ^ (m + 1 + 1) := by rw [pow_succ]; ring

private lemma explicitStep_claim16205 (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (m + 1) - m - 2 < 2 ^ ((m + 1) + 1) - (m + 1) - 2 := by
  have hp : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    ring
  rw [show (m + 1) + 1 = m + 2 by omega, hp]
  have h := pow_two_ge_strong_claim16205 m (by omega)
  omega

private lemma reindexed_sum_claim16205 (m n : ℕ) :
    ∑ j ∈ Finset.range m, ((n + j + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (n + j + 1) =
      (1 / (2 : ℚ) ^ n) *
        (∑ j ∈ Finset.range m, ((n + j + 1 : ℕ) : ℚ) * (1 / (2 : ℚ)) ^ (j + 1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv, show n + j + 1 = n + (j + 1) by omega, pow_add]
  push_cast
  field_simp
  have hunit : (2 : ℚ) ^ (j + 1) * (1 / (2 : ℚ)) ^ (j + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hunit]

/-- Claim 16205: infinitely many positive integers have finite distinct
representations, with the displayed representation for every `m ≥ 2`. -/
theorem explicitDistinctRepresentation_claim16205 :
    Set.Infinite (Set.range (fun m : ℕ =>
      2 ^ ((m + 2) + 1) - (m + 2) - 2)) ∧
    (∀ m : ℕ, 0 < 2 ^ ((m + 2) + 1) - (m + 2) - 2) ∧
    (∀ m : ℕ, 2 ≤ m →
      let n : ℕ := 2 ^ (m + 1) - m - 2
      0 < n ∧
        ((n : ℚ) / (2 : ℚ) ^ n =
          ∑ j ∈ Finset.range m,
            ((n + j + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (n + j + 1)) ∧
        (∀ j ∈ Finset.range m, n < n + j + 1 ∧ n + j + 1 ≤ n + m) ∧
        (∀ j, j ∈ Finset.range m → ∀ k, k ∈ Finset.range m →
          n + j + 1 = n + k + 1 → j = k)) := by
  constructor
  · apply Set.infinite_range_of_injective
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro m
    simpa using explicitStep_claim16205 (m + 2) (by omega)
  · constructor
    · intro m
      have h := pow_two_ge_strong_claim16205 (m + 2) (by omega)
      omega
    · intro m hm
      dsimp
      let n : ℕ := 2 ^ (m + 1) - m - 2
      have hpow : m + 2 ≤ 2 ^ (m + 1) := by
        have := pow_two_ge_strong_claim16205 m (by omega)
        omega
      have hstrong : m + 3 ≤ 2 ^ (m + 1) :=
        pow_two_ge_strong_claim16205 m (by omega)
      have hn_pos : 0 < n := by
        dsimp [n]
        omega
      have hn_add : n + m + 2 = 2 ^ (m + 1) := by
        dsimp [n]
        omega
      have hcalc :
          ∑ j ∈ Finset.range m,
            ((n + j + 1 : ℕ) : ℚ) * (1 / (2 : ℚ)) ^ (j + 1) = n := by
        calc
          _ = n * (∑ j ∈ Finset.range m, (1 / (2 : ℚ)) ^ (j + 1)) +
              ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℚ) * (1 / (2 : ℚ)) ^ (j + 1) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro j hj
                push_cast
                ring
          _ = n * (1 - (1 / (2 : ℚ)) ^ m) +
              (2 - (m + 2 : ℚ) * (1 / (2 : ℚ)) ^ m) := by
                rw [sum_inv_two_pow_shift_claim16205,
                  sum_j_inv_two_pow_shift_claim16205]
          _ = n + (2 - ((n : ℚ) + m + 2) * (1 / (2 : ℚ)) ^ m) := by ring
          _ = n := by
                have hn_add_q : (n : ℚ) + m + 2 = (2 : ℚ) ^ (m + 1) := by
                  exact_mod_cast hn_add
                have hpow_q : (2 : ℚ) ^ (m + 1) = 2 * (2 : ℚ) ^ m := by
                  rw [pow_succ]
                  ring
                rw [hn_add_q, hpow_q]
                have hunit : (2 : ℚ) ^ m * (1 / (2 : ℚ)) ^ m = 1 := by
                  rw [← mul_pow]
                  norm_num
                calc
                  (n : ℚ) + (2 - 2 * (2 : ℚ) ^ m * (1 / (2 : ℚ)) ^ m) =
                      n + (2 - 2 * ((2 : ℚ) ^ m * (1 / (2 : ℚ)) ^ m)) := by ring
                  _ = n := by rw [hunit]; ring
      have heq :
          (n : ℚ) / (2 : ℚ) ^ n =
            ∑ j ∈ Finset.range m,
              ((n + j + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (n + j + 1) := by
        rw [reindexed_sum_claim16205, hcalc]
        ring
      refine ⟨hn_pos, heq, ?_, ?_⟩
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        omega
      · intro j k hj hk h_eq
        omega

end MathlibPlus.NumberTheory
