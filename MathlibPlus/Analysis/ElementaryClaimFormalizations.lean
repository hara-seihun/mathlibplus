import Mathlib

namespace MathlibPlus.Analysis.ElementaryClaimFormalizations

/-- Claim 15655: the norm of an exterior-square determinant is bounded by the
sum of the norms of its two monomials. -/
theorem exteriorSquareNormBound (x y z : ℂ) :
    ‖x * z - y ^ 2‖ ≤ ‖x‖ * ‖z‖ + ‖y‖ ^ 2 := by
  calc
    ‖x * z - y ^ 2‖ ≤ ‖x * z‖ + ‖y ^ 2‖ := norm_sub_le _ _
    _ = ‖x‖ * ‖z‖ + ‖y‖ ^ 2 := by rw [norm_mul, norm_pow]

/-- Claim 2319: the endpoint multiplier has the stated elementary bounds. -/
theorem endpointMultiplierInequality (m : ℕ) (s : ℝ)
    (_hm : 1 ≤ m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ 1 - (1 - s) ^ m ∧ 1 - (1 - s) ^ m ≤ (m : ℝ) * s := by
  have hq0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hq1 : 1 - s ≤ 1 := by linarith
  have hpow_le : ∀ k : ℕ, (1 - s) ^ k ≤ 1 :=
    fun k => pow_le_one₀ hq0 hq1
  have hpow_nonneg : ∀ k : ℕ, 0 ≤ (1 - s) ^ k :=
    fun k => pow_nonneg hq0 k
  have hbound : ∀ k : ℕ,
      0 ≤ 1 - (1 - s) ^ k ∧ 1 - (1 - s) ^ k ≤ (k : ℝ) * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hdecomp :
            1 - (1 - s) ^ k * (1 - s) =
              (1 - (1 - s) ^ k) + (1 - s) ^ k * s := by
          ring
        rw [hdecomp]
        constructor
        · exact add_nonneg ih.1 (mul_nonneg (hpow_nonneg k) hs0)
        · have hmul : (1 - s) ^ k * s ≤ s := by
            calc
              (1 - s) ^ k * s ≤ 1 * s :=
                mul_le_mul_of_nonneg_right (hpow_le k) hs0
              _ = s := one_mul s
          calc
            (1 - (1 - s) ^ k) + (1 - s) ^ k * s
                ≤ (k : ℝ) * s + s := add_le_add ih.2 hmul
            _ = ((k + 1 : ℕ) : ℝ) * s := by
              norm_num [Nat.cast_add]
              ring
  exact hbound m

/-- Claim 18064: the displayed numerator vanishes at both endpoints. -/
theorem cancellationAtZeroAndOne (n : ℕ) (hn : 1 ≤ n) :
    let F : ℝ → ℝ := fun s =>
      ((n : ℝ) + s) * ((n + 1 : ℕ) : ℝ) ^ (-s) -
        (n : ℝ) ^ (1 - s)
    F 0 = 0 ∧ F 1 = 0 := by
  dsimp
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  constructor
  · simp [Real.rpow_zero]
  · rw [show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero]
    field_simp
    norm_num [Nat.cast_add]

end MathlibPlus.Analysis.ElementaryClaimFormalizations
