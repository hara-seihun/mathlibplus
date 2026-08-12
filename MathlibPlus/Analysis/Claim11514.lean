import Mathlib.Analysis.SpecificLimits.Normed

namespace MathlibPlus.Analysis

open scoped BigOperators

/-- Claim 11514: the odd-displacement part of the binomially weighted
packet series has the exact closed form used for adverse packets. -/
theorem claim11514_oddPacketSum (M : ℕ) (hM : 0 < M) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ,
        if Odd n then
          ((n + (M - 1)).choose (M - 1) : ℝ) * q ^ n
        else 0) =
      (1 / (1 - q) ^ M - 1 / (1 + q) ^ M) / 2 := by
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hqneg : ‖-q‖ < 1 := by simpa [norm_neg] using hq
  have hsumq := hasSum_choose_mul_geometric_of_norm_lt_one (M - 1) hq
  have hsumneg := hasSum_choose_mul_geometric_of_norm_lt_one (M - 1) hqneg
  have hsumq' :
      HasSum (fun n : ℕ ↦
        ((n + (M - 1)).choose (M - 1) : ℝ) * q ^ n)
        (1 / (1 - q) ^ M) := by
    simpa [Nat.sub_add_cancel hM] using hsumq
  have hsumneg' :
      HasSum (fun n : ℕ ↦
        ((n + (M - 1)).choose (M - 1) : ℝ) * (-q) ^ n)
        (1 / (1 + q) ^ M) := by
    simpa [Nat.sub_add_cancel hM, sub_neg_eq_add] using hsumneg
  have hpoint : ∀ n : ℕ,
      (if Odd n then
          ((n + (M - 1)).choose (M - 1) : ℝ) * q ^ n
        else 0) =
        ((((n + (M - 1)).choose (M - 1) : ℝ) * q ^ n) -
          (((n + (M - 1)).choose (M - 1) : ℝ) * (-q) ^ n)) / 2 := by
    intro n
    rcases Nat.even_or_odd n with hn | hn
    · have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
      simp [hnot, hn.neg_pow]
    · simp [hn, hn.neg_pow]
  have hsumdiff := (hsumq'.sub hsumneg').div_const 2
  have hsumodd : HasSum
      (fun n : ℕ ↦
        if Odd n then
          ((n + (M - 1)).choose (M - 1) : ℝ) * q ^ n
        else 0)
      ((1 / (1 - q) ^ M - 1 / (1 + q) ^ M) / 2) :=
    hsumdiff.congr_fun (fun n ↦ hpoint n)
  exact hsumodd.tsum_eq

end MathlibPlus.Analysis
