import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The elementary prime-power depth sum, with the index shifted so that the
original range `a ≥ 1` is represented by `a + 2` for `a : ℕ`. -/
theorem primePowerDepthSum
    (q : ℝ) (hq : 1 < q) :
    (∑' a : ℕ, ((a + 2 : ℕ) : ℝ) / q ^ (a + 2)) =
      (2 * q - 1) / (q * (q - 1) ^ 2) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrnorm : ‖q⁻¹‖ < (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqpos)]
    exact (inv_lt_one₀ hqpos).2 hq
  let r : ℝ := q⁻¹
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := r)
      (by simpa [r] using hrnorm)).summable
  have hsum := hs.sum_add_tsum_nat_add 2
  have htotal : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one (r := r)
      (by simpa [r] using hrnorm)
  have htail : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) =
      r / (1 - r) ^ 2 - r := by
    have hsum' := hsum
    rw [htotal] at hsum'
    have hsum2 : r + (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) =
        r / (1 - r) ^ 2 := by
      simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm] using hsum'
    apply (eq_sub_iff_add_eq).2
    calc
      (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) + r =
          r + (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) := by ring
      _ = r / (1 - r) ^ 2 := hsum2
  calc
    (∑' a : ℕ, ((a + 2 : ℕ) : ℝ) / q ^ (a + 2)) =
        ∑' a : ℕ, ((a + 2 : ℕ) : ℝ) * r ^ (a + 2) := by
      apply tsum_congr
      intro a
      simp only [r]
      have hqne : q ≠ 0 := ne_of_gt hqpos
      rw [div_eq_mul_inv, ← inv_pow]
    _ = r / (1 - r) ^ 2 - r := htail
    _ = (2 * q - 1) / (q * (q - 1) ^ 2) := by
      dsimp [r]
      have hqne : q ≠ 0 := ne_of_gt hqpos
      have hq1ne : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
      field_simp [hqne, hq1ne]
      ring

end MathlibPlus.Analysis
