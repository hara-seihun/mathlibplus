import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.NumberTheory

open PowerSeries

/-- The coefficient calculation used for the formal local scattering
logarithm in admitted claim 12313. -/
private lemma coeff_logOf_one_sub_smul_X (a : ℚ) (k : ℕ) (hk : 0 < k) :
    coeff k (logOf (1 - a • X : PowerSeries ℚ)) =
      (-1 : ℚ) ^ (k + 1) / k * (-a) ^ k := by
  rw [logOf_eq]
  have hsub : (1 - a • X : PowerSeries ℚ) - 1 = -(a • X) := by
    simp only [sub_eq_add_neg]
    abel_nf
  have hneg : (-(a • X) : PowerSeries ℚ) = (-a) • X := by simp
  have smul_X_pow (c : ℚ) (n : ℕ) :
      (c • X : PowerSeries ℚ) ^ n = c ^ n • X ^ n := by
    rw [smul_eq_C_mul, mul_pow]
    rw [← map_pow, ← smul_eq_C_mul]
  rw [hsub, hneg, coeff_subst' (HasSubst.smul_X' (-a))]
  rw [finsum_eq_single _ k]
  · rw [smul_X_pow]
    simp [coeff_log, hk.ne']
  · intro b hb
    rw [smul_X_pow]
    simp [Ne.symm hb]

/-- In the formal Euler variable, the coefficient of degree `k` in one
scattering logarithm is `(1-p⁻ᵏ)/k`, rather than `1/k`.  The displayed
formal logarithm is written as the difference of the numerator and
denominator logarithms; no analytic convergence assertion is included. -/
theorem claim12313_formalScatteringLog_coeff (p k : ℕ) (_hp : Nat.Prime p)
    (hk : 0 < k) :
    coeff k
        (logOf (1 - (p : ℚ)⁻¹ • X) - logOf (1 - X) : PowerSeries ℚ) =
      (1 - ((p : ℚ)⁻¹) ^ k) / k := by
  rw [map_sub, coeff_logOf_one_sub_smul_X ((p : ℚ)⁻¹) k hk]
  have hone : coeff k (logOf (1 - X : PowerSeries ℚ)) =
      (-1 : ℚ) ^ (k + 1) / k * (-1) ^ k := by
    simpa using (coeff_logOf_one_sub_smul_X 1 k hk)
  rw [hone]
  have hsignEven : (-1 : ℚ) ^ (k + k) = 1 := by
    rw [pow_add, ← mul_pow]
    norm_num
  have hsignOdd : (-1 : ℚ) ^ (k + 1) * (-1 : ℚ) ^ k = -1 := by
    rw [← pow_add, show (k + 1) + k = (k + k) + 1 by omega, pow_succ,
      hsignEven]
    norm_num
  have hA : (-1 : ℚ) ^ (k + 1) * (-(p : ℚ)⁻¹) ^ k =
      -((p : ℚ)⁻¹) ^ k := by
    have hnegpow : (-(p : ℚ)⁻¹ : ℚ) ^ k =
        (-1 : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k := neg_pow ((p : ℚ)⁻¹) k
    rw [hnegpow]
    calc
      (-1 : ℚ) ^ (k + 1) *
          ((-1 : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k) =
          ((-1 : ℚ) ^ (k + 1) * (-1 : ℚ) ^ k) *
            ((p : ℚ)⁻¹) ^ k := by ring
      _ = -((p : ℚ)⁻¹) ^ k := by rw [hsignOdd]; simp
  calc
    (-1 : ℚ) ^ (k + 1) / k * (-(p : ℚ)⁻¹) ^ k -
        (-1 : ℚ) ^ (k + 1) / k * (-1) ^ k =
        ((-1 : ℚ) ^ (k + 1) * (-(p : ℚ)⁻¹) ^ k -
          (-1 : ℚ) ^ (k + 1) * (-1 : ℚ) ^ k) / k := by ring
    _ = (-((p : ℚ)⁻¹) ^ k - (-1 : ℚ)) / k := by rw [hA, hsignOdd]
    _ = (1 - ((p : ℚ)⁻¹) ^ k) / k := by ring

end MathlibPlus.NumberTheory
