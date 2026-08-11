import MathlibPlus.Basic

open Filter
open Asymptotics
open scoped Topology

namespace MathlibPlus.Asymptotics.SublinearDegree

/-- Claim 3102 under the natural degree/index interpretation: if `B L ≥ 1`
and the weighted quotient tends to zero, then the unweighted quotient tends to
zero and the degree is little-o of the index. -/
theorem degree_div_tendsto_zero
    (B : ℕ → ℝ) (d : ℕ → ℕ) (k : ℕ)
    (hB : ∀ L : ℕ, 1 ≤ B L)
    (hweighted : Tendsto
      (fun L : ℕ => (B L) ^ k * (d L : ℝ) / (L : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => (d L : ℝ) / (L : ℝ)) atTop (𝓝 0) ∧
      (fun L : ℕ => (d L : ℝ)) =o[atTop] (fun L : ℕ => (L : ℝ)) := by
  have hquot : Tendsto
      (fun L : ℕ => (d L : ℝ) / (L : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun L : ℕ => (B L) ^ k * (d L : ℝ) / (L : ℝ)) ?_ ?_ hweighted
    · filter_upwards [eventually_ge_atTop 1] with L hL
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with L hL
      have hLpos : (0 : ℝ) < (L : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt hL)
      have hpow : (1 : ℝ) ≤ (B L) ^ k := one_le_pow₀ (hB L)
      apply (div_le_div_iff_of_pos_right hLpos).2
      simpa using (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg (d L)))
  have hzero : ∀ᶠ L : ℕ in atTop, (L : ℝ) = 0 → (d L : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with L hL hden
    have hLne : (L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hL))
    exact (hLne hden).elim
  exact ⟨hquot, (isLittleO_iff_tendsto' hzero).2 hquot⟩

end MathlibPlus.Asymptotics.SublinearDegree
