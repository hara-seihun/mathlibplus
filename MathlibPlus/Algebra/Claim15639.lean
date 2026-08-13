import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim15639

/-- Claim 15639: the source's displayed ratio is interpreted over `ℝ`, its
    natural domain for the division and inequality. -/
theorem adjacentChannelWeightRatio_claim15639
    (scale order : ℝ) (hscale : 1 ≤ scale) (horder : 0 ≤ order)
    (horder_le : order ≤ scale) :
    scale / (order + 1) ≥ 1 / 2 := by
  have hden : 0 < order + 1 := by linarith
  apply (le_div_iff₀ hden).2
  linarith

end MathlibPlus.Algebra.Claim15639
