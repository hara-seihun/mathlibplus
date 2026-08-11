import Mathlib

namespace MathlibPlus.Analysis.Claim15639

/-- The adjacent channel-weight ratio is at least one half on the stated
natural-number range. -/
theorem channelWeightRatio_ge_half
    {scale order : ℕ} (hscale : 1 ≤ scale) (horder : order ≤ scale) :
    (1 / 2 : ℝ) ≤ (scale : ℝ) / ((order : ℝ) + 1) := by
  have hden : (0 : ℝ) < (order : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hden).2
  have hscaleR : (1 : ℝ) ≤ scale := by exact_mod_cast hscale
  have horderR : (order : ℝ) ≤ scale := by exact_mod_cast horder
  nlinarith

end MathlibPlus.Analysis.Claim15639
