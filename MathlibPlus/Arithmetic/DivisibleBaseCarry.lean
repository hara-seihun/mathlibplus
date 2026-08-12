import Mathlib

namespace MathlibPlus.Arithmetic.DivisibleBaseCarry

/-- Claim 10545: for a divisible base, the usual carry quotient is exactly
 the shifted real interval from the source statement. -/
theorem carry_interval
    (m q c k d : ℕ)
    (hm : 0 < m) (hq : 0 < q)
    (_hc : c < m) (_hk : k < m) (_hd : d < m * q) :
    ((m * d + c) / (m * q) = k ↔
      (k : ℝ) * q - (c : ℝ) / m ≤ d ∧
        (d : ℝ) < (k + 1 : ℕ) * q - (c : ℝ) / m) := by
  have hmq : 0 < m * q := Nat.mul_pos hm hq
  have hdiv_iff :
      (m * d + c) / (m * q) = k ↔
        k * (m * q) ≤ m * d + c ∧
          m * d + c < (k + 1) * (m * q) := by
    constructor
    · intro h
      constructor
      · have h' := Nat.mul_div_le (m * d + c) (m * q)
        simpa [h, Nat.mul_comm] using h'
      · have h' := Nat.lt_mul_div_succ (m * d + c) hmq
        rw [h] at h'
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using h'
    · rintro ⟨hlo, hhi⟩
      exact Nat.div_eq_of_lt_le hlo hhi
  rw [hdiv_iff]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : (c : ℝ) / m * m = c := by
    field_simp
  constructor
  · rintro ⟨hlo, hhi⟩
    have hloR0 : ((k * (m * q) : ℕ) : ℝ) ≤ (m * d + c : ℕ) := by
      exact_mod_cast hlo
    have hhiR0 : ((m * d + c : ℕ) : ℝ) < ((k + 1) * (m * q) : ℕ) := by
      exact_mod_cast hhi
    have hloR : (k : ℝ) * (m : ℝ) * q ≤ (m : ℝ) * d + c := by
      simpa [Nat.cast_mul, mul_assoc] using hloR0
    have hhiR : (m : ℝ) * d + c < ((k + 1 : ℕ) : ℝ) * (m : ℝ) * q := by
      simpa [Nat.cast_mul, mul_assoc] using hhiR0
    constructor <;> nlinarith [hloR, hhiR, hdiv]
  · rintro ⟨hlo, hhi⟩
    have hloR : (k : ℝ) * (m : ℝ) * q ≤ (m : ℝ) * d + c := by
      nlinarith [hlo, hdiv]
    have hhiR : (m : ℝ) * d + c < ((k + 1 : ℕ) : ℝ) * (m : ℝ) * q := by
      nlinarith [hhi, hdiv]
    have hloR' :
        ((k * (m * q) : ℕ) : ℝ) ≤ ((m * d + c : ℕ) : ℝ) := by
      simpa [Nat.cast_mul, Nat.cast_add, mul_assoc] using hloR
    have hhiR' :
        ((m * d + c : ℕ) : ℝ) < (((k + 1) * (m * q) : ℕ) : ℝ) := by
      simpa [Nat.cast_mul, Nat.cast_add, mul_assoc] using hhiR
    have hlo : k * (m * q) ≤ m * d + c := Nat.cast_le.mp hloR'
    have hhi : m * d + c < (k + 1) * (m * q) := Nat.cast_lt.mp hhiR'
    exact ⟨hlo, hhi⟩

/-- Claim 10545: at zero incoming carry the shifted interval is the ordinary
half-open block `[kq,(k+1)q)`. -/
theorem carry_interval_zero
    (m q k d : ℕ)
    (hm : 0 < m) (hq : 0 < q)
    (hk : k < m) (hd : d < m * q) :
    ((m * d) / (m * q) = k ↔
      (k : ℝ) * q ≤ d ∧ (d : ℝ) < (k + 1 : ℕ) * q) := by
  simpa using carry_interval m q 0 k d hm hq (Nat.zero_lt_of_lt hm) hk hd

/-- Claim 10545: for a nonzero valid incoming carry, the shift is strictly
between zero and one. -/
theorem carry_interval_nonzero_shift
    (m c : ℕ) (hc₀ : 0 < c) (hcm : c < m) :
    0 < (c : ℝ) / m ∧ (c : ℝ) / m < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hcm)
  constructor
  · positivity
  · have hcR : (c : ℝ) < m := by exact_mod_cast hcm
    exact (div_lt_iff₀ hmR).2 (by simpa using hcR)

end MathlibPlus.Arithmetic.DivisibleBaseCarry
