import Mathlib

namespace MathlibPlus.Analysis.Claim1215

/-- For `x > 1`, the prime-counting right-hand side is strictly increasing in
its coefficient whenever both denominators are positive. -/
theorem rhs_strictMonoInCoefficient_claim1215 {x c₁ c₂ : ℝ}
    (hx : 1 < x) (hcc : c₁ < c₂)
    (h₁ : 0 < Real.log x - 1 - c₁ / Real.log x)
    (h₂ : 0 < Real.log x - 1 - c₂ / Real.log x) :
    x / (Real.log x - 1 - c₁ / Real.log x) <
      x / (Real.log x - 1 - c₂ / Real.log x) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hquot : c₁ / Real.log x < c₂ / Real.log x := by
    exact (div_lt_div_iff₀ hlog hlog).2 (by nlinarith)
  have hden : Real.log x - 1 - c₂ / Real.log x <
      Real.log x - 1 - c₁ / Real.log x := by
    linarith
  apply (div_lt_div_iff₀ h₁ h₂).2
  exact mul_lt_mul_of_pos_left hden hxpos

/-- A bound valid with coefficient `1.149` transfers to the larger coefficient
`1.14900031` on any tail where the latter denominator is positive. -/
theorem transfer_to_repairedCoefficient_claim1215
    {f : ℝ → ℝ} {X : ℝ}
    (hX : ∀ x, X ≤ x → 1 < x)
    (hbase : ∀ x, X ≤ x →
      0 < Real.log x - 1 - (1.149 : ℝ) / Real.log x →
      f x < x / (Real.log x - 1 - (1.149 : ℝ) / Real.log x)) :
    ∀ x, X ≤ x →
      0 < Real.log x - 1 - (1.14900031 : ℝ) / Real.log x →
      f x < x / (Real.log x - 1 - (1.14900031 : ℝ) / Real.log x) := by
  intro x hx h₂
  have hxgt : 1 < x := hX x hx
  have hlog : 0 < Real.log x := Real.log_pos hxgt
  have hcc : (1.149 : ℝ) < 1.14900031 := by norm_num
  have hquot : (1.149 : ℝ) / Real.log x <
      (1.14900031 : ℝ) / Real.log x := by
    exact (div_lt_div_iff₀ hlog hlog).2 (by nlinarith)
  have h₁ : 0 < Real.log x - 1 - (1.149 : ℝ) / Real.log x := by
    linarith
  exact (hbase x hx h₁).trans
    (rhs_strictMonoInCoefficient_claim1215 hxgt hcc h₁ h₂)

end MathlibPlus.Analysis.Claim1215
