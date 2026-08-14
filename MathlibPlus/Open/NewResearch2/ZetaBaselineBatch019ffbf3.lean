import Mathlib

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain

noncomputable section

private def baselineRealZeta (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re
private def baselineNormalizedZeta (s : ℝ) : ℝ := (s - 1) * baselineRealZeta s
private def baselineTwoPow (s : ℝ) : ℝ := Real.rpow 2 s

/-- Claim 1685: the fractional-part integral baselines. -/
def claim1685_fractionalPartIntegralBaselines : Prop :=
  ∀ s : ℝ, 3 < s →
    s - 1 + (s + 3) / baselineTwoPow (s + 1) < baselineNormalizedZeta s ∧
      baselineNormalizedZeta s < s - 1 + (s + 1) / baselineTwoPow s

end

end MathlibPlus.Open.NewResearch2.FormalizationDrain
