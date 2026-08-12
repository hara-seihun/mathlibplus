import Mathlib

namespace MathlibPlus.Analysis.Claim13013

/-- Exact normalized-ratio identity at the c₂-only threshold.  The threshold
condition is exposed as `hthreshold`; the source's `V(x)` construction is not
silently reconstructed. -/
theorem denominator_ratio_identity_claim13013
    (q c₁ c₂ V : ℝ) (hq : 1 < q)
    (hthreshold : c₂ * V =
      (Real.sqrt q * (Real.log q) ^ 2 / 100) *
        ((2 : ℝ) ^ (-(1 : ℝ) / 3))) :
    (c₁ * Real.log q + c₂ * V) /
        (Real.sqrt q * (Real.log q) ^ 2 / 100) =
      (2 : ℝ) ^ (-(1 : ℝ) / 3) +
        100 * c₁ / (Real.sqrt q * Real.log q) := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hl : 0 < Real.log q := Real.log_pos hq
  rw [hthreshold]
  field_simp [ne_of_gt hs, ne_of_gt hl]
  ring

/-- The residual c₁-term is strictly decreasing in q>1 for c₁>0. -/
theorem denominator_ratio_term_strictAnti_claim13013
    (q₁ q₂ c₁ : ℝ) (hc₁ : 0 < c₁) (hq₁ : 1 < q₁)
    (h₁₂ : q₁ < q₂) :
    100 * c₁ / (Real.sqrt q₂ * Real.log q₂) <
      100 * c₁ / (Real.sqrt q₁ * Real.log q₁) := by
  have hq₁0 : 0 < q₁ := by linarith
  have hq₂0 : 0 < q₂ := lt_trans hq₁0 h₁₂
  have hs₁ : 0 < Real.sqrt q₁ := Real.sqrt_pos.2 hq₁0
  have hs₂ : 0 < Real.sqrt q₂ := Real.sqrt_pos.2 hq₂0
  have hss : Real.sqrt q₁ < Real.sqrt q₂ :=
    Real.sqrt_lt_sqrt (le_of_lt hq₁0) h₁₂
  have hl₁ : 0 < Real.log q₁ := Real.log_pos hq₁
  have hll : Real.log q₁ < Real.log q₂ := by
    exact Real.strictMonoOn_log (by exact hq₁0) (by exact hq₂0) h₁₂
  have hprod : Real.sqrt q₁ * Real.log q₁ <
      Real.sqrt q₂ * Real.log q₂ := by
    calc
      Real.sqrt q₁ * Real.log q₁ < Real.sqrt q₂ * Real.log q₁ :=
        mul_lt_mul_of_pos_right hss hl₁
      _ < Real.sqrt q₂ * Real.log q₂ :=
        mul_lt_mul_of_pos_left hll hs₂
  have hn : 0 < 100 * c₁ := by positivity
  apply (div_lt_div_iff₀
    (mul_pos hs₂ (Real.log_pos (by linarith : 1 < q₂)))
    (mul_pos hs₁ hl₁)).2
  exact mul_lt_mul_of_pos_left hprod hn

end MathlibPlus.Analysis.Claim13013
