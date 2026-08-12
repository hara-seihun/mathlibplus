import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 57480: the paired fibre lower bound for `0 ≤ a < 1`. -/
theorem pairedFibreInequality_claim57480
    (a : ℝ) (u v : ℂ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    max ‖u - v‖ (((1 - a) / (1 + a)) * ‖u + v‖) ≥
      (1 - a) * ‖u‖ := by
  let κ : ℝ := (1 - a) / (1 + a)
  let B : ℝ := max ‖u - v‖ (κ * ‖u + v‖)
  have hδ : 0 < 1 - a := by linarith
  have hden : 0 < 1 + a := by linarith
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos hδ hden
  have hdiff : ‖u - v‖ ≤ B := by
    exact le_max_left _ _
  have hsum : κ * ‖u + v‖ ≤ B := by
    exact le_max_right _ _
  have hplus : ‖u + v‖ ≤ B / κ := by
    apply (le_div_iff₀ hκ).2
    simpa [mul_comm] using hsum
  have hnorm : 2 * ‖u‖ ≤ ‖u - v‖ + ‖u + v‖ := by
    calc
      2 * ‖u‖ = ‖(2 : ℂ) * u‖ := by
        rw [norm_mul]
        norm_num
      _ = ‖(u - v) + (u + v)‖ := by
        congr 1
        ring
      _ ≤ ‖u - v‖ + ‖u + v‖ := norm_add_le _ _
  have hcombined : 2 * ‖u‖ ≤ B + B / κ := by
    exact le_trans hnorm (add_le_add hdiff hplus)
  have hscaled : (1 - a) * (2 * ‖u‖) ≤ (1 - a) * (B + B / κ) :=
    mul_le_mul_of_nonneg_left hcombined (le_of_lt hδ)
  have hrecip : 1 / κ = (1 + a) / (1 - a) := by
    dsimp [κ]
    field_simp
  rw [div_eq_mul_inv] at hscaled
  have hinv : κ⁻¹ = (1 + a) / (1 - a) := by
    simpa [one_div] using hrecip
  rw [hinv] at hscaled
  have hrewrite :
      (1 - a) * (B + B * ((1 + a) / (1 - a))) = 2 * B := by
    field_simp [ne_of_gt hδ]
    ring
  rw [hrewrite] at hscaled
  have htarget : (1 - a) * ‖u‖ ≤ B := by
    nlinarith [hscaled]
  dsimp [B, κ] at htarget ⊢
  exact htarget

end MathlibPlus.Analysis
