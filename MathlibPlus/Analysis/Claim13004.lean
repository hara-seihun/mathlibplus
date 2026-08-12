import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim13004

/-- Cancellation of the scale in the weighted geometric mean. -/
theorem scale_identity
    (A B lam : ℝ) (hA : 0 < A) (hB : 0 < B) (hlam : 0 < lam) :
    (A / lam ^ 2) ^ (1 / 3 : ℝ) * ((B * lam / 2) ^ (1 / 3 : ℝ)) ^ 2 =
      A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) / (2 : ℝ) ^ (2 / 3 : ℝ) := by
  rw [Real.div_rpow (le_of_lt hA) (sq_nonneg lam) (1 / 3 : ℝ)]
  rw [Real.div_rpow (mul_nonneg (le_of_lt hB) (le_of_lt hlam))
    (by norm_num) (1 / 3 : ℝ)]
  rw [Real.mul_rpow (le_of_lt hB) (le_of_lt hlam)]
  have hpow_l : (lam ^ 2 : ℝ) ^ (1 / 3 : ℝ) = lam ^ (2 / 3 : ℝ) := by
    have h := (Real.rpow_mul (le_of_lt hlam) (2 : ℝ) (1 / 3 : ℝ)).symm
    norm_num at h ⊢
    exact h
  rw [hpow_l]
  have hpow : (B ^ (1 / 3 : ℝ) * lam ^ (1 / 3 : ℝ) /
      (2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 =
      (B ^ (1 / 3 : ℝ)) ^ 2 * (lam ^ (1 / 3 : ℝ)) ^ 2 /
        ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by ring
  rw [hpow]
  have hBpow : (B ^ (1 / 3 : ℝ)) ^ 2 = B ^ (2 / 3 : ℝ) := by
    have h := (Real.rpow_mul (le_of_lt hB) (1 / 3 : ℝ) (2 : ℝ)).symm
    norm_num at h ⊢
    exact h
  have hlam_pow : (lam ^ (1 / 3 : ℝ)) ^ 2 = lam ^ (2 / 3 : ℝ) := by
    have h := (Real.rpow_mul (le_of_lt hlam) (1 / 3 : ℝ) (2 : ℝ)).symm
    norm_num at h ⊢
    exact h
  have h2pow : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have h := (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
      (1 / 3 : ℝ) (2 : ℝ)).symm
    norm_num at h ⊢
    exact h
  rw [hBpow, hlam_pow, h2pow]
  field_simp

/-- The sharp weighted arithmetic--geometric mean bound underlying the
elimination of the scale parameter. -/
theorem sharp_elimination_of_lambda
    (A B lam : ℝ) (hA : 0 < A) (hB : 0 < B) (hlam : 0 < lam) :
    A / lam ^ 2 + B * lam ≥
      3 / (2 : ℝ) ^ (2 / 3 : ℝ) * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) := by
  let p : ℝ := (A / lam ^ 2) ^ (1 / 3 : ℝ)
  let q : ℝ := (B * lam / 2) ^ (1 / 3 : ℝ)
  have hp0 : 0 ≤ p := Real.rpow_nonneg (by positivity) _
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hp3 : p ^ (3 : ℕ) = A / lam ^ 2 := by
    dsimp [p]
    have h := Real.rpow_inv_natCast_pow (x := A / lam ^ 2)
      (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hq3 : q ^ (3 : ℕ) = B * lam / 2 := by
    dsimp [q]
    have h := Real.rpow_inv_natCast_pow (x := B * lam / 2)
      (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hineq : 3 * p * q ^ 2 ≤ p ^ 3 + 2 * q ^ 3 := by
    have hfactor : 0 ≤ (p - q) ^ 2 * (p + 2 * q) := by
      exact mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith [hfactor]
  have hpq : p * q ^ 2 =
      A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) / (2 : ℝ) ^ (2 / 3 : ℝ) := by
    exact scale_identity A B lam hA hB hlam
  calc
    3 / (2 : ℝ) ^ (2 / 3 : ℝ) * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ)
        = 3 * (A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) /
          (2 : ℝ) ^ (2 / 3 : ℝ)) := by ring
    _ = 3 * (p * q ^ 2) := by rw [hpq]
    _ ≤ p ^ 3 + 2 * q ^ 3 := by simpa [mul_assoc] using hineq
    _ = A / lam ^ 2 + B * lam := by rw [hp3, hq3]; ring

/-- The lower bound is attained by the positive scale `(2A/B)^(1/3)`, so it
is a genuine minimum over positive scales. -/
theorem sharp_elimination_is_attained
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ lam : ℝ, 0 < lam ∧
      A / lam ^ 2 + B * lam =
        3 / (2 : ℝ) ^ (2 / 3 : ℝ) * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) := by
  let lam : ℝ := (2 * A / B) ^ (1 / 3 : ℝ)
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hlam3 : lam ^ (3 : ℕ) = 2 * A / B := by
    dsimp [lam]
    have h := Real.rpow_inv_natCast_pow (x := 2 * A / B)
      (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hrel : lam ^ 3 * B = 2 * A := by
    rw [hlam3]
    field_simp
  have hbase : A / lam ^ 2 = B * lam / 2 := by
    field_simp
    nlinarith [hrel]
  let p : ℝ := (A / lam ^ 2) ^ (1 / 3 : ℝ)
  let q : ℝ := (B * lam / 2) ^ (1 / 3 : ℝ)
  have hpq_eq : p = q := by
    dsimp [p, q]
    rw [hbase]
  have hq3 : q ^ (3 : ℕ) = B * lam / 2 := by
    dsimp [q]
    have h := Real.rpow_inv_natCast_pow (x := B * lam / 2)
      (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hq_const : q ^ 3 =
      A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) / (2 : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      q ^ 3 = p * q ^ 2 := by rw [hpq_eq]; ring
      _ = A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) /
        (2 : ℝ) ^ (2 / 3 : ℝ) := by
          exact scale_identity A B lam hA hB hlam
  refine ⟨lam, hlam, ?_⟩
  calc
    A / lam ^ 2 + B * lam = 3 * (B * lam / 2) := by rw [hbase]; ring
    _ = 3 * q ^ 3 := by rw [hq3]
    _ = 3 * (A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) /
        (2 : ℝ) ^ (2 / 3 : ℝ)) := by rw [hq_const]
    _ = 3 / (2 : ℝ) ^ (2 / 3 : ℝ) * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ) := by ring

end MathlibPlus.Analysis.Claim13004
