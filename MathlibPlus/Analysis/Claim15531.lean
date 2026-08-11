import Mathlib

namespace MathlibPlus.Analysis.Claim15531

/-- The displayed archimedean density factor is strictly negative on the
source ray `t ≥ log 2`. -/
theorem kappa_neg {t : ℝ} (ht : Real.log 2 ≤ t) :
    t * ((Real.exp (2 * t) - 1)⁻¹ - Real.exp t) < 0 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htpos : 0 < t := lt_of_lt_of_le hlog ht
  have hexp : (2 : ℝ) ≤ Real.exp t := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by
        rw [Real.exp_log] <;> norm_num
      _ ≤ Real.exp t := (Real.exp_le_exp).2 ht
  have hden : 0 < Real.exp (2 * t) - 1 := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    nlinarith
  have hden3 : 3 ≤ Real.exp (2 * t) - 1 := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    nlinarith
  have hprod : 1 < Real.exp t * (Real.exp (2 * t) - 1) := by
    have hmul : (2 : ℝ) * 3 ≤ Real.exp t * (Real.exp (2 * t) - 1) :=
      mul_le_mul hexp hden3 (by positivity) (by positivity)
    nlinarith
  have hfrac : (Real.exp (2 * t) - 1)⁻¹ < Real.exp t := by
    have hfrac' : 1 / (Real.exp (2 * t) - 1) < Real.exp t :=
      (div_lt_iff₀ hden).2 hprod
    simpa [one_div] using hfrac'
  nlinarith

end MathlibPlus.Analysis.Claim15531
