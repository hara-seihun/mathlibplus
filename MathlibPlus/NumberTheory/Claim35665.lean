import Mathlib

namespace MathlibPlus.NumberTheory

/--
Claim 35665.  For `n_m = 2^(m+1) - m - 2`, the consecutive support
`{n_m + 1, ..., n_m + m}` gives the exact finite representation
`n_m / 2^n_m`.  The statement also records that the indices form a strictly
increasing family.
-/
theorem claim35665_consecutiveDyadicRepresentations :
    let f : ℕ → ℕ := fun m => 2 ^ (m + 1) - m - 2
    StrictMono f ∧
      ∀ m : ℕ, 1 ≤ m →
        let n : ℕ := f m
        (n + m + 2 = 2 ^ (m + 1)) ∧
          (∑ j ∈ Finset.range m,
              ((n + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (n + (j + 1))) =
            (n : ℚ) / (2 : ℚ) ^ n := by
  dsimp
  have hpow_lower : ∀ m : ℕ, m + 2 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      calc
        m + 1 + 2 ≤ (m + 2) + 1 := by omega
        _ ≤ 2 ^ (m + 1) + 1 := by omega
        _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := by
          have hp : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
          omega
        _ = 2 ^ (m + 2) := by
          have h := Nat.two_pow_succ (m + 1)
          convert h.symm using 1 <;> omega
  have hweighted (a m : ℕ) :
      (∑ j ∈ Finset.range m,
          ((a + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (j + 1)) =
        (a : ℚ) * (1 - 1 / (2 : ℚ) ^ m) +
          2 - (m + 2 : ℚ) / (2 : ℚ) ^ m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have hp : (2 : ℚ) ^ m ≠ 0 := by positivity
      have hps : (2 : ℚ) ^ (m + 1) = 2 ^ m + 2 ^ m := by
        rw [pow_succ]
        norm_num
        ring
      rw [hps]
      field_simp
      push_cast
      ring
  have hrepresentation (a m : ℕ) (hrel : a + m + 2 = 2 ^ (m + 1)) :
      (∑ j ∈ Finset.range m,
          ((a + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (a + (j + 1))) =
        (a : ℚ) / (2 : ℚ) ^ a := by
    have hpa : (2 : ℚ) ^ a ≠ 0 := by positivity
    have hpm : (2 : ℚ) ^ m ≠ 0 := by positivity
    calc
      (∑ j ∈ Finset.range m,
          ((a + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (a + (j + 1))) =
          ∑ j ∈ Finset.range m,
            (1 / (2 : ℚ) ^ a) *
              (((a + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        field_simp
      _ = (1 / (2 : ℚ) ^ a) *
            (∑ j ∈ Finset.range m,
              ((a + (j + 1) : ℕ) : ℚ) / (2 : ℚ) ^ (j + 1)) := by
        rw [Finset.mul_sum]
      _ = (1 / (2 : ℚ) ^ a) *
            ((a : ℚ) * (1 - 1 / (2 : ℚ) ^ m) +
              2 - (m + 2 : ℚ) / (2 : ℚ) ^ m) := by rw [hweighted]
      _ = (a : ℚ) / (2 : ℚ) ^ a := by
        have hrelQ : (a : ℚ) + (m : ℚ) + 2 = (2 : ℚ) ^ (m + 1) := by
          exact_mod_cast hrel
        have hrelQ' : (a : ℚ) + (m + 2 : ℚ) = (2 : ℚ) ^ m * 2 := by
          rw [← pow_succ]
          convert hrelQ using 1 <;> ring
        have hinner :
            (a : ℚ) * (1 - 1 / (2 : ℚ) ^ m) +
                2 - (m + 2 : ℚ) / (2 : ℚ) ^ m = a := by
          calc
            (a : ℚ) * (1 - 1 / (2 : ℚ) ^ m) +
                2 - (m + 2 : ℚ) / (2 : ℚ) ^ m =
                (a : ℚ) + 2 - (a + (m + 2 : ℚ)) / (2 : ℚ) ^ m := by
                  field_simp
                  ring
            _ = (a : ℚ) + 2 - ((2 : ℚ) ^ m * 2) / (2 : ℚ) ^ m := by
                  rw [hrelQ']
            _ = a := by
                  field_simp
                  ring
        rw [hinner]
        ring
  constructor
  · apply strictMono_nat_of_lt_succ
    intro m
    have hm : m + 2 ≤ 2 ^ (m + 1) := hpow_lower m
    have hm1 : (m + 1) + 2 ≤ 2 ^ ((m + 1) + 1) := hpow_lower (m + 1)
    have hpow : 2 ^ ((m + 1) + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
      rw [Nat.two_pow_succ]
    omega
  · intro m _hm
    have hrel : (2 ^ (m + 1) - m - 2) + m + 2 = 2 ^ (m + 1) := by
      have h := hpow_lower m
      omega
    refine ⟨hrel, ?_⟩
    exact hrepresentation (2 ^ (m + 1) - m - 2) m hrel

end MathlibPlus.NumberTheory
