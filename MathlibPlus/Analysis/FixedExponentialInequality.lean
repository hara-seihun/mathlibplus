import Mathlib

namespace MathlibPlus.Analysis

/-!
# A fixed-exponential versus sigma-log-sigma inequality

This file records the fully quantified real inequality in admitted claim 3624.
-/

/-- Claim 3624: the stated logarithmic hypothesis gives a strict exponential
upper bound. -/
theorem fixedExponentialVsSigmaLogSigma (A B σ : ℝ) (hB : 0 < B)
    (hσ : 1 ≤ σ)
    (h : 2 * A + 2 * |Real.log B| + 2 ≤ Real.log σ) :
    B * Real.exp (A * σ) < Real.exp (σ * Real.log σ / 2) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hA : A ≤ Real.log σ / 2 - |Real.log B| - 1 := by
    linarith
  have hAσ : A * σ ≤ (Real.log σ / 2 - |Real.log B| - 1) * σ := by
    exact mul_le_mul_of_nonneg_right hA (le_of_lt hσ0)
  have hprod : 0 ≤ (σ - 1) * |Real.log B| := by
    exact mul_nonneg (sub_nonneg.mpr hσ) (abs_nonneg _)
  have hcore : Real.log B + A * σ < σ * Real.log σ / 2 := by
    nlinarith [le_abs_self (Real.log B), hprod]
  calc
    B * Real.exp (A * σ) = Real.exp (Real.log B + A * σ) := by
      rw [Real.exp_add, Real.exp_log hB]
    _ < Real.exp (σ * Real.log σ / 2) := Real.exp_lt_exp.mpr hcore

end MathlibPlus.Analysis
