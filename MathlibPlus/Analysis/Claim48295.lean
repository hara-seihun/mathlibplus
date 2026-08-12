import Mathlib

open BigOperators
open scoped BigOperators

namespace MathlibPlus.Analysis.Claim48295

/-- The coefficient in the finite-support bound. -/
noncomputable def c (s : ℕ) : ℝ :=
  ((s + 1 : ℕ) : ℝ) * ((2 * s + 1 : ℕ) : ℝ) / (6 * (s : ℝ))

theorem probability_sum_sq_le_c
    {s : ℕ} (hs : 0 < s) (R : Fin s → ℝ)
    (hR : ∀ j, 0 < R j) (hSum : ∑ j, R j = 1) :
    ∑ j, (R j) ^ 2 ≤ c s := by
  have hle (j : Fin s) : R j ≤ 1 := by
    have hrest : 0 ≤ ∑ i ∈ (Finset.univ : Finset (Fin s)).erase j, R i := by
      exact Finset.sum_nonneg (fun i hi => (hR i).le)
    have hsplit : R j + ∑ i ∈ (Finset.univ : Finset (Fin s)).erase j, R i = 1 := by
      rw [← hSum]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      ac_rfl
    linarith
  have hsq : ∑ j, (R j) ^ 2 ≤ 1 := by
    calc
      ∑ j, (R j) ^ 2 ≤ ∑ j, R j := by
        apply Finset.sum_le_sum
        intro j hj
        nlinarith [(hR j).le, hle j]
      _ = 1 := hSum
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : 0 < (6 : ℝ) * s := by positivity
  have hc : (1 : ℝ) ≤ c s := by
    unfold c
    apply (le_div_iff₀ hden).2
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have htwo : 0 ≤ 2 * (s : ℝ) - 1 := by nlinarith
    have hone : 0 ≤ (s : ℝ) - 1 := by nlinarith
    have hpoly : 0 ≤ (2 * (s : ℝ) - 1) * ((s : ℝ) - 1) :=
      mul_nonneg htwo hone
    nlinarith
  exact hsq.trans hc

theorem c_three : c 3 = (14 : ℝ) / 9 := by
  norm_num [c]

theorem c_four : c 4 = (15 : ℝ) / 8 := by
  norm_num [c]

theorem c_lt_two_of_one_le_of_le_four {s : ℕ} (hs₁ : 1 ≤ s)
    (hs₄ : s ≤ 4) : c s < 2 := by
  interval_cases s <;> norm_num [c]

end MathlibPlus.Analysis.Claim48295
