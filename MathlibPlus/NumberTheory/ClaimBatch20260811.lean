import Mathlib

open Filter

namespace MathlibPlus.NumberTheory.ClaimBatch20260811

/-- Claim 35771: the target-index sequence is eventually increasing and tends
 to infinity. -/
theorem targetIndicesTendToInfinity_claim35771 :
    Filter.Tendsto (fun m : ℕ => 2 ^ (m + 1) - m - 2) atTop atTop ∧
      (∀ᶠ m : ℕ in atTop,
        2 ^ (m + 1) - m - 2 < 2 ^ (m + 2) - (m + 1) - 2) := by
  have hpow_le : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
          _ ≤ 2 ^ n + 2 ^ n := by
            have : 0 < 2 ^ n := pow_pos (by norm_num) _
            omega
          _ = 2 ^ (n + 1) := by ring
  constructor
  · refine Filter.tendsto_atTop_atTop.2 ?_
    intro b
    refine ⟨b + 3, ?_⟩
    intro m hm
    have hpow : b + m + 2 ≤ 2 ^ (m + 1) := by
      have hm3 : 3 ≤ m := by omega
      have hmexp : m ≤ 2 ^ m := hpow_le m
      have hdouble : 2 * m ≤ 2 ^ (m + 1) := by
        calc
          2 * m ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 hmexp
          _ = 2 ^ (m + 1) := by ring
      omega
    omega
  · filter_upwards [eventually_ge_atTop 2] with m hm
    have hmexp : m ≤ 2 ^ m := hpow_le m
    have hpow : m + 3 ≤ 2 ^ (m + 1) := by
      by_cases htwo : m = 2
      · subst m
        norm_num
      · have hm3 : 3 ≤ m := by omega
        calc
          m + 3 ≤ 2 * m := by omega
          _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 hmexp
          _ = 2 ^ (m + 1) := by ring
    rw [show 2 ^ (m + 2) = 2 * 2 ^ (m + 1) by ring]
    omega

end MathlibPlus.NumberTheory.ClaimBatch20260811
