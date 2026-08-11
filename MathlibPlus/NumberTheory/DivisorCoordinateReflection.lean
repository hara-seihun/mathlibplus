import Mathlib

namespace MathlibPlus.NumberTheory

/--
Claim 17944.  For positive `k` and positive `m ∣ k`, the coordinate
`ell_{k,m} = (1/2) * log(k / m^2)` changes sign under complementary divisors.
The quotient in the complementary index is the natural-number quotient.
-/
theorem divisorCoordinate_reflection
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (hmk : m ∣ k) :
    let ell : ℕ → ℕ → ℝ :=
      fun k m ↦ (1 / 2 : ℝ) * Real.log ((k : ℝ) / (m : ℝ) ^ 2)
    ell k (k / m) = -ell k m := by
  dsimp
  have hkr : 0 < k / m := Nat.div_pos (Nat.le_of_dvd hk hmk) hm
  have hK : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hM : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hQ : ((k / m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hkr)
  have hkq : (k : ℝ) = (m : ℝ) * ((k / m : ℕ) : ℝ) := by
    calc
      (k : ℝ) = ((m * (k / m) : ℕ) : ℝ) := by
        rw [Nat.mul_div_cancel' hmk]
      _ = (m : ℝ) * ((k / m : ℕ) : ℝ) := by norm_num
  have hratio :
      (k : ℝ) / ((k / m : ℕ) : ℝ) ^ 2 =
        (m : ℝ) ^ 2 / (k : ℝ) := by
    field_simp [hK, hM, hQ]
    nlinarith [hkq]
  rw [hratio, Real.log_div (pow_ne_zero 2 hM) hK,
    Real.log_div hK (pow_ne_zero 2 hM), Real.log_pow]
  ring

end MathlibPlus.NumberTheory
