import MathlibPlus.Open.Analysis.Claims14059_14062_14064_14067

open MeasureTheory
open Set

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 14061: the positive logarithmic tilt and its probability measure. -/
def logarithmicTiltProbabilityLaw_claim14061 : Prop :=
  let q : ℝ → ℝ := fun x => 1 / x - 1 / (Real.exp x - 1)
  let F : ℂ → ℂ := fun s =>
    ∫ x in Ioi (0 : ℝ),
      Complex.cpow (x : ℂ) (s - (1 : ℂ)) * (q x : ℂ)
  let Freal : ℝ → ℝ := fun σ => (F (σ : ℂ)).re
  let density : ℝ → ℝ → ENNReal := fun σ y =>
    ENNReal.ofReal
      (Real.exp (σ * y) * q (Real.exp y) / Freal σ)
  let μ : ℝ → Measure ℝ := fun σ => volume.withDensity (density σ)
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    0 < Freal σ ∧
      (F (σ : ℂ)).im = 0 ∧
        IsProbabilityMeasure (μ σ)

end

end MathlibPlus.Open.Analysis
