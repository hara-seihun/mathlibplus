import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0247Repair.Claim19174

noncomputable section

/-- Equal even and odd interval norms force zero Lorentz defect on the
amplitude-supported part of a common positive fusion. -/
def equalEvenOddIntervalNormsRequireSaturation : Prop :=
  ∀ (A E O : ℝ → ℝ) (w : ℝ),
    0 < w →
    (∀ ω : ℝ, 0 ≤ A ω) →
    (∀ ω : ℝ, |O ω| ≤ E ω) →
    Integrable (fun ω : ℝ => A ω * E ω) →
    Integrable (fun ω : ℝ => A ω * O ω) →
    w = ∫ ω : ℝ, A ω * E ω →
    (w = ∫ ω : ℝ, A ω * O ω ∨
      -w = ∫ ω : ℝ, A ω * O ω) →
    |∫ ω : ℝ, A ω * O ω| = ∫ ω : ℝ, A ω * E ω ∧
      (∫ ω : ℝ, A ω * E ω = w) ∧
      (∀ᵐ ω : ℝ ∂MeasureTheory.volume,
        A ω ≠ 0 → E ω = |O ω|)

end

end MathlibPlus.Open.NewResearch2.R0247Repair.Claim19174
