import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

private lemma offset_sum_formula_icc (x : ℚ) (m : ℕ) :
    (∑ d ∈ Finset.Icc 1 m,
      (x + (d : ℚ)) / (2 : ℚ) ^ d) =
      x * (1 - 1 / (2 : ℚ) ^ m) + 2 - (m + 2 : ℚ) / (2 : ℚ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      simp only [pow_succ]
      push_cast
      field_simp
      ring

private lemma linear_le_pow (m : ℕ) : m + 2 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      nlinarith

/-- The displayed family in claim 47280 satisfies its finite offset equation.
The sum is over the exact offset set `D_m = {1, ..., m}`. -/
theorem offset_equation_claim47280 (m : ℕ) (_hm : 1 ≤ m) :
    (∑ d ∈ Finset.Icc 1 m,
      (((2 ^ (m + 1) - m - 2 : ℕ) : ℚ) + (d : ℚ)) /
        (2 : ℚ) ^ d) =
      ((2 ^ (m + 1) - m - 2 : ℕ) : ℚ) := by
  have h1 : m ≤ 2 ^ (m + 1) := by
    exact le_trans (Nat.le_add_right m 2) (linear_le_pow m)
  have h2 : 2 ≤ 2 ^ (m + 1) - m := by
    rw [Nat.le_sub_iff_add_le h1]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using linear_le_pow m
  have hn :
      ((2 ^ (m + 1) - m - 2 : ℕ) : ℚ) =
        (2 : ℚ) ^ (m + 1) - m - 2 := by
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    norm_num
  rw [hn, offset_sum_formula_icc]
  rw [pow_succ]
  field_simp
  ring

/-- For `m ≥ 2`, the exact offset set has at least two summands. -/
theorem offset_family_two_or_more_claim47280 (m : ℕ) (hm : 2 ≤ m) :
    2 ≤ (Finset.Icc 1 m).card := by
  simpa using hm

private lemma two_mul_add_four_lt_pow (m : ℕ) : 2 * m + 4 < 2 ^ (m + 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      nlinarith

/-- The values in the family of claim 47280 are unbounded. -/
theorem offset_family_unbounded_claim47280 :
    ∀ B : ℕ, ∃ m : ℕ, B < 2 ^ (m + 1) - m - 2 := by
  intro B
  refine ⟨B + 2, ?_⟩
  have hpow : 2 * B + 4 < 2 ^ (B + 3) := two_mul_add_four_lt_pow B
  change B < 2 ^ (B + 3) - (B + 2) - 2
  apply (Nat.lt_sub_iff_add_lt).2
  apply (Nat.lt_sub_iff_add_lt).2
  nlinarith

end MathlibPlus.NumberTheory
