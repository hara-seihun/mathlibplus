import Mathlib

namespace MathlibPlus.Algebra

open Polynomial

lemma rowUniformCoefficientKernel_coeff_one_add_X (N k : ℕ) :
    ((1 + X : ℚ[X]) ^ N).coeff k = (Nat.choose N k : ℚ) := by
  exact Polynomial.coeff_one_add_X_pow ℚ N k

lemma rowUniformCoefficientKernel_coeff_one_add_two_X (N k : ℕ) :
    ((1 + 2 * X : ℚ[X]) * (1 + X) ^ N).coeff k =
      (Nat.choose N k : ℚ) +
        2 * if k = 0 then 0 else (Nat.choose N (k - 1) : ℚ) := by
  have htwo : (2 : ℚ[X]) = Polynomial.C 2 := (Polynomial.C_eq_natCast 2).symm
  have hpoly :
      (1 + 2 * X : ℚ[X]) * (1 + X) ^ N =
        (1 + X) ^ N + (2 * X) * (1 + X) ^ N := by
    ring
  rw [hpoly, Polynomial.coeff_add]
  rw [rowUniformCoefficientKernel_coeff_one_add_X]
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
    rw [htwo]
    simp only [mul_assoc]
    rw [Polynomial.coeff_C_mul]
    have hcoeff :
        (X * (1 + X) ^ N : ℚ[X]).coeff k =
          ((1 + X) ^ N).coeff (k - 1) := by
      rw [← hk']
      exact Polynomial.coeff_X_mul _ _
    rw [hcoeff, rowUniformCoefficientKernel_coeff_one_add_X]
    simp [hk]

lemma rowUniformCoefficientKernel_choose_ratio_aux (M k : ℕ) (hM : 0 < M) :
    (M : ℚ) * ((Nat.choose (M - 1) k : ℚ) +
      2 * if k = 0 then 0 else (Nat.choose (M - 1) (k - 1) : ℚ)) =
      (M + k : ℚ) * (Nat.choose M k : ℚ) := by
  by_cases hk : k = 0
  · simp [hk]
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hk' : k' + 1 - 1 = k' := by omega
    have hM' : M - 1 + 1 = M := by omega
    have hpascalN :
        Nat.choose M (k' + 1) =
          Nat.choose (M - 1) k' + Nat.choose (M - 1) (k' + 1) := by
      simpa [hM'] using (Nat.choose_succ_succ' (M - 1) k')
    have hmulN :
        M * Nat.choose (M - 1) k' =
          Nat.choose M (k' + 1) * (k' + 1) := by
      simpa [hM'] using (Nat.add_one_mul_choose_eq (M - 1) k')
    have hpascalQ :
        (Nat.choose M (k' + 1) : ℚ) =
          (Nat.choose (M - 1) k' : ℚ) +
            (Nat.choose (M - 1) (k' + 1) : ℚ) := by
      exact_mod_cast hpascalN
    have hmulQ :
        (M : ℚ) * (Nat.choose (M - 1) k' : ℚ) =
          (Nat.choose M (k' + 1) : ℚ) * (k' + 1 : ℚ) := by
      exact_mod_cast hmulN
    simp [hk, hk']
    nlinarith [hpascalQ, hmulQ]

/-- Claim 42803: the coefficient of the row-uniform kernel has the stated
closed form.  The zero coefficient convention is explicit when the column
offset exceeds the requested coefficient. -/
theorem rowUniformCoefficientKernel_claim42803 (R q s : ℕ) (hR : 0 < R + s) :
    let K : ℚ :=
      ((1 + 2 * X) * X ^ s * (1 + X) ^ (R + s - 1 : ℕ)).coeff q
    K = if s ≤ q then
      ((R + q : ℚ) / (R + s : ℚ)) * (Nat.choose (R + s) (q - s) : ℚ)
    else 0 := by
  dsimp
  have hpoly :
      (1 + 2 * X : ℚ[X]) * X ^ s * (1 + X) ^ (R + s - 1 : ℕ) =
        ((1 + 2 * X) * (1 + X) ^ (R + s - 1 : ℕ)) * X ^ s := by
    ring
  rw [hpoly, Polynomial.coeff_mul_X_pow']
  by_cases hs : s ≤ q
  · simp only [if_pos hs]
    have hM : 0 < R + s := hR
    have hMcast : (R + s : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hM)
    have hshift : R + s + (q - s) = R + q := by omega
    rw [rowUniformCoefficientKernel_coeff_one_add_two_X]
    have hratio := rowUniformCoefficientKernel_choose_ratio_aux (R + s) (q - s) hM
    have hshiftQ :
        (R + s : ℚ) + ((q - s : ℕ) : ℚ) = (R + q : ℕ) := by
      exact_mod_cast hshift
    have hratio' :
        ((Nat.choose (R + s - 1) (q - s) : ℚ) +
          2 * if q - s = 0 then 0 else
            (Nat.choose (R + s - 1) (q - s - 1) : ℚ)) * (R + s : ℚ) =
          (R + q : ℚ) * (Nat.choose (R + s) (q - s) : ℚ) := by
      calc
        _ = ((R + s : ℚ) + ((q - s : ℕ) : ℚ)) *
            (Nat.choose (R + s) (q - s) : ℚ) := by
          simpa [mul_comm] using hratio
        _ = _ := by rw [hshiftQ]; norm_num [Nat.cast_add]
    field_simp [hMcast]
    nlinarith [hratio']
  · simp only [if_neg hs]

end MathlibPlus.Algebra
