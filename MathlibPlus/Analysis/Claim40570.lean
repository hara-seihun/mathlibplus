import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim40570

/-- The displayed Euclidean-transfer domain lies below the minimal parent
state and sends its child state into the invariant interval. -/
theorem discreteLogFour_transferInvariant_claim40570
    (x z : ℝ)
    (hx_lower : (3 : ℝ) / 16 < x)
    (hx_upper : x < (3 : ℝ) / 10)
    (hz_lower : 3 * (1 - x) / 13 < z)
    (hz_x : z < x)
    (hz_third : z < (1 - x) / 3) :
    x < (3 : ℝ) / 10 ∧
      z < x ∧
      x + 3 * z < 1 ∧
      (3 : ℝ) / 10 < z / (1 - x - z) ∧
      z / (1 - x - z) < (1 : ℝ) / 2 := by
  have hx_pos : 0 < x := by linarith
  have hone_minus_x : 0 < 1 - x := by linarith
  have hz_pos : 0 < z := by linarith
  have hden : 0 < 1 - x - z := by
    linarith
  refine ⟨hx_upper, hz_x, ?_, ?_, ?_⟩
  · linarith
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

end MathlibPlus.Analysis.Claim40570
