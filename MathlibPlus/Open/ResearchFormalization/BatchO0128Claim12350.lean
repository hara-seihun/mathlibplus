import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.BatchO0128

/-- A positive Gaussian-scale mixture with a negative order-two trace determinant. -/
def claim12350 : Prop :=
  let F : ℝ → ℝ := fun t => Real.exp (-t ^ 2) + 10 * Real.exp (-2 * t ^ 2)
  let H₂ : ℝ → ℝ := fun t =>
    (deriv F t) ^ 2 - F t * deriv (deriv F) t
  let μ : Measure ℝ :=
    (1 / (11 : ENNReal)) •
      (Measure.dirac (1 : ℝ) + (10 : ENNReal) • Measure.dirac (2 : ℝ))
  MeasureTheory.IsProbabilityMeasure μ ∧
    (∀ t : ℝ,
      F t / 11 = ∫ x : ℝ, Real.exp (-x * t ^ 2) ∂μ) ∧
    H₂ 0 = 462 ∧ 0 < H₂ 0 ∧
    (∀ t : ℝ, t ^ 2 = (16 : ℝ) / 5 →
      -((1781305062153140484482914 : ℝ) / (10 : ℝ) ^ 28) < H₂ t ∧
        H₂ t < -((1781305062153140484482913 : ℝ) / (10 : ℝ) ^ 28) ∧
        H₂ t < 0)

end MathlibPlus.Open.ResearchFormalization.BatchO0128
