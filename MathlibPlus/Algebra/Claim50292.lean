import Mathlib

namespace MathlibPlus.Algebra.Claim50292

open Polynomial

private lemma scaledCoefficient (s k : ℕ) :
    ((1 + C (2 : ℚ) * (X : ℚ[X])) ^ s).coeff k =
      (2 : ℚ) ^ k * (s.choose k : ℚ) := by
  have hpoly : (1 + C (2 : ℚ) * (X : ℚ[X])) =
      C (2 : ℚ) * (X + C (1 / 2 : ℚ)) := by
    rw [mul_add]
    simp [← C_mul]
    ring
  rw [hpoly, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  by_cases h : k ≤ s
  · have hp : (2 : ℚ) ^ s * (1 / 2 : ℚ) ^ (s - k) = (2 : ℚ) ^ k := by
      have hpow : (1 / 2 : ℚ) ^ (s - k) =
          ((2 : ℚ) ^ (s - k))⁻¹ := by
        rw [show (1 / 2 : ℚ) = (2 : ℚ)⁻¹ by norm_num, inv_pow]
      rw [hpow, pow_sub₀ (2 : ℚ) (by norm_num) h]
      field_simp
    rw [← mul_assoc, hp]
  · have hchoose : s.choose k = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)
    simp [hchoose]

private lemma shiftedCoefficient (h k : ℕ) :
    ((X : ℚ[X]) * (1 + X) ^ h : ℚ[X]).coeff k =
      if 0 < k then (h.choose (k - 1) : ℚ) else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [coeff_X_mul, coeff_one_add_X_pow]
    simp

/-- Claim 50292 (source R-3809): the two summands of
`(1 + 2 x)^s + x (1 + x)^h` have the exact binomial coefficient rows
`2^k * choose s k` and `choose h (k-1)`, with the out-of-range `k = 0`
case represented explicitly as zero. -/
theorem claim50292_coefficientDecomposition (s h k : ℕ) (_hh : h ≤ s) :
    let H : ℚ[X] :=
      (1 + C (2 : ℚ) * (X : ℚ[X])) ^ s +
        (X : ℚ[X]) * (1 + X) ^ h
    H.coeff k =
      (2 : ℚ) ^ k * (s.choose k : ℚ) +
        (if 0 < k then (h.choose (k - 1) : ℚ) else 0) := by
  dsimp
  rw [coeff_add, scaledCoefficient, shiftedCoefficient]

end MathlibPlus.Algebra.Claim50292
