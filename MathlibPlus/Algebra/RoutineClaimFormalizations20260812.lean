import Mathlib

namespace MathlibPlus.Algebra.Claim23413

theorem uniqueDyadicNormalization (w : ℕ → ℚ)
    (h0 : w 0 = 1)
    (hstep : ∀ n, w (n + 1) = w n / 2) :
    ∀ n, w n = 1 / (2 : ℚ) ^ n := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      rw [hstep, ih, pow_succ]
      ring

theorem normalizedBinomialMassAndShift (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℚ) / (2 : ℚ) ^ n) = 1 ∧
    ∀ k : ℕ,
      (Nat.choose (n + 1) k : ℚ) / (2 : ℚ) ^ (n + 1) =
        ((Nat.choose n k : ℚ) / (2 : ℚ) ^ n +
          (if k = 0 then 0 else
            (Nat.choose n (k - 1) : ℚ) / (2 : ℚ) ^ n)) / 2 := by
  constructor
  · rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
    norm_num
  · intro k
    cases k with
    | zero =>
      rw [Nat.choose_zero_right, Nat.choose_zero_right]
      rw [pow_succ]
      norm_num [div_eq_mul_inv]
      ac_rfl
    | succ k =>
      simp only [Nat.choose_succ_succ, Nat.succ_sub_one]
      rw [pow_succ]
      norm_num [div_eq_mul_inv, pow_succ]
      ring

end MathlibPlus.Algebra.Claim23413

namespace MathlibPlus.Algebra.Claim43033

/-- The formal-real square obstruction in the displayed rational-profile relation. -/
theorem nonzeroThirdFunctional_claim43033 {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (V r w : K) (Λ₃ : K → K)
    (hV : V ≠ 0) (hzero : Λ₃ 0 = 0)
    (hrel : V * Λ₃ w = r ^ 2 + V ^ 4 / 12) :
    Λ₃ w ≠ 0 ∧ w ≠ 0 := by
  have hV2 : 0 < V ^ 2 := sq_pos_of_ne_zero hV
  have hV4 : 0 < V ^ 4 := by positivity
  have hL : Λ₃ w ≠ 0 := by
    intro hL
    rw [hL] at hrel
    have hr : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  constructor
  · exact hL
  · intro hw
    apply hL
    rw [hw, hzero]

end MathlibPlus.Algebra.Claim43033
