import Mathlib

namespace MathlibPlus.NumberTheory

private theorem one_le_two_pow (n : ℕ) : (1 : ℚ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

private theorem two_pow_succ_sub_one_pos (n : ℕ) : (0 : ℚ) < 2 ^ (n + 1) - 1 := by
  rw [pow_succ]
  nlinarith [one_le_two_pow n]

/-- The two displayed rational expressions in Claim 50192 are identical. -/
theorem complementaryFormula_identity_claim50192
    (r h : ℕ) (hh : 0 < h) :
    ((2 : ℚ) ^ (r + h) + h) / ((2 : ℚ) ^ h - 1) - r - 1 =
      (2 : ℚ) ^ r - r - 1 + ((2 : ℚ) ^ r + h) / ((2 : ℚ) ^ h - 1) := by
  have hne : (2 : ℚ) ^ h - 1 ≠ 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
    exact ne_of_gt (two_pow_succ_sub_one_pos k)
  field_simp [hne] <;> rw [pow_add] <;> ring

private theorem three_dvd_two_pow_two_mul_add_two (k : ℕ) :
    (3 : ℤ) ∣ (2 : ℤ) ^ (2 * k) + 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hmul : (3 : ℤ) ∣ 4 * ((2 : ℤ) ^ (2 * k) + 2) :=
        dvd_mul_of_dvd_right ih 4
      have hconst : (3 : ℤ) ∣ 6 := by norm_num
      have hsub : (3 : ℤ) ∣ 4 * ((2 : ℤ) ^ (2 * k) + 2) - 6 :=
        dvd_sub hmul hconst
      convert hsub using 1 <;> rw [Nat.mul_succ, pow_add] <;> ring

/-- The displayed complementary equation has an integral start exactly under
    the divisibility condition in Claim 50192. -/
theorem complementaryStart_integral_iff_claim50192
    (r h : ℕ) (hr : 0 < r) (hh : 0 < h) :
    ((2 : ℤ) ^ h - 1 ∣ (2 : ℤ) ^ r + h) ↔
      ∃ N : ℤ,
        ((2 : ℤ) ^ h - 1) * (N + r + 1) = (2 : ℤ) ^ (r + h) + h := by
  have hdecomp : (2 : ℤ) ^ (r + h) + h =
      ((2 : ℤ) ^ h - 1) * (2 : ℤ) ^ r + ((2 : ℤ) ^ r + h) := by
    rw [pow_add]
    ring
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + (2 : ℤ) ^ r - r - 1, ?_⟩
    rw [hdecomp, hk]
    ring
  · rintro ⟨N, hN⟩
    refine ⟨N + r + 1 - (2 : ℤ) ^ r, ?_⟩
    calc
      (2 : ℤ) ^ r + h =
          ((2 : ℤ) ^ h - 1) * (N + r + 1) -
            ((2 : ℤ) ^ h - 1) * (2 : ℤ) ^ r := by
              rw [hN]
              ring
      _ = ((2 : ℤ) ^ h - 1) * (N + r + 1 - (2 : ℤ) ^ r) := by ring

/-- The `h=1` specialization from Claim 50192. -/
theorem complementaryStart_h_one_claim50192
    (r : ℕ) (hr : 0 < r) :
    ∃ N : ℤ,
      ((2 : ℤ) ^ 1 - 1) * (N + r + 1) = (2 : ℤ) ^ (r + 1) + 1 ∧
        N = (2 : ℤ) ^ (r + 1) - r := by
  refine ⟨(2 : ℤ) ^ (r + 1) - r, ?_⟩
  constructor <;> norm_num [pow_succ] <;> ring

/-- The even-`r`, `h=2` family from Claim 50192. -/
theorem complementaryStart_h_two_even_claim50192
    (r : ℕ) (hr : 0 < r) (heven : Even r) :
    ∃ N : ℤ,
      ((2 : ℤ) ^ 2 - 1) * (N + r + 1) = (2 : ℤ) ^ (r + 2) + 2 := by
  obtain ⟨k, rfl⟩ := heven
  have hd : (2 : ℤ) ^ 2 - 1 ∣ (2 : ℤ) ^ (k + k) + 2 := by
    norm_num
    simpa [two_mul] using three_dvd_two_pow_two_mul_add_two k
  exact (complementaryStart_integral_iff_claim50192 (k + k) 2 (by omega) (by norm_num)).mp hd

end MathlibPlus.NumberTheory
