import Mathlib

namespace MathlibPlus.Analysis.Claim57703

theorem derivative_bound_claim57703
    (m : ℕ) (hm : 3 ≤ m) (E : ℝ)
    (hE : E ≤ 8 * (m : ℝ) + 56 / 3 -
      4 * (m : ℝ) ^ 5 / ((m : ℝ) ^ 2 + 1)) :
    E < -(m : ℝ) ^ 3 := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : 0 < (m : ℝ) := by linarith
  have hden : 0 < (m : ℝ) ^ 2 + 1 := by positivity
  have hm2 : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - 3)]
  have hm3 : 9 * (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    have hmul := mul_nonneg hpos.le (sub_nonneg.mpr hm2)
    nlinarith
  have hfrac : (13 / 5 : ℝ) ≤
      (3 * (m : ℝ) ^ 2 - 1) / ((m : ℝ) ^ 2 + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hm2]
  have hpoly :
      8 * (m : ℝ) + 56 / 3 - (m : ℝ) ^ 3 * (13 / 5 : ℝ) < 0 := by
    nlinarith [hm3]
  have hmain :
      8 * (m : ℝ) + 56 / 3 -
          (m : ℝ) ^ 3 *
            ((3 * (m : ℝ) ^ 2 - 1) / ((m : ℝ) ^ 2 + 1)) < 0 := by
    have hmul := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ (m : ℝ) ^ 3)
    nlinarith
  have hrewrite :
      8 * (m : ℝ) + 56 / 3 -
          4 * (m : ℝ) ^ 5 / ((m : ℝ) ^ 2 + 1) + (m : ℝ) ^ 3 =
        8 * (m : ℝ) + 56 / 3 -
          (m : ℝ) ^ 3 *
            ((3 * (m : ℝ) ^ 2 - 1) / ((m : ℝ) ^ 2 + 1)) := by
    field_simp [ne_of_gt hden]
    ring
  nlinarith [hE, hmain, hrewrite]

end MathlibPlus.Analysis.Claim57703
