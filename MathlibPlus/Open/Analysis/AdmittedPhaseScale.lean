import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def phaseScale (σ t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.log Real.pi -
      (Complex.digamma
        ((6 : ℂ) + ((σ : ℂ) - (t : ℂ) * Complex.I) / 2)).re)

noncomputable def phaseScaleMagnitude (σ t : ℝ) : ℝ :=
  -phaseScale σ t

noncomputable def phaseScaleLowerBound : ℝ :=
  (1 / 2 : ℝ) *
    ((Complex.digamma ((25 / 4 : ℝ) : ℂ)).re - Real.log Real.pi)

def canonicalPhaseScaleGloballyPositive : Prop :=
  ∀ σ t : ℝ,
    (1 / 2 : ℝ) ≤ σ → σ ≤ 1 →
      phaseScale σ t < 0 ∧
        phaseScaleMagnitude σ t = -phaseScale σ t ∧
        phaseScaleLowerBound ≤ phaseScaleMagnitude σ t ∧
        0 < phaseScaleLowerBound

end MathlibPlus.Open.Analysis
