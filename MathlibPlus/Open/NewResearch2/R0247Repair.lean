import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0247Repair

noncomputable section

/-- Claim 19176: a nonzero equal-norm interval cycle cannot be reproduced by a
positive common-amplitude fusion with finite rapidity coordinates. The even
and odd sector weights are the two integrals appearing in the packet. -/
def claim19176_intervalwisePositiveFusionNoGo : Prop :=
  ∀ (A ξ : ℝ → ℝ) (w : ℝ),
    0 < w →
    (∀ ω : ℝ, 0 ≤ A ω) →
    Integrable (fun ω : ℝ => A ω * Real.cosh (ξ ω)) →
    Integrable (fun ω : ℝ => A ω * Real.sinh (ξ ω)) →
    w = ∫ ω : ℝ, A ω * Real.cosh (ξ ω) →
    ((w = ∫ ω : ℝ, A ω * Real.sinh (ξ ω)) ∨
      (-w = ∫ ω : ℝ, A ω * Real.sinh (ξ ω))) →
    False

end

end MathlibPlus.Open.NewResearch2.R0247Repair
