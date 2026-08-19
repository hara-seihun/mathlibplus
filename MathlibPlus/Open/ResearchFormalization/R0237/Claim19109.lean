import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0237.Claim19109

/-- Source-bound statement for the quadratic numerator: the positive leading
coefficient, the displayed discriminant, its two distinct real roots, and the
corresponding normalized reciprocal-parameter polynomial are all retained in
one proposition. -/
def largeMiddleCoefficientRoots : Prop :=
  ∀ (p b : ℝ),
    0 < p →
    2 * Real.sqrt p < b →
    let numerator : ℝ → ℝ := fun t => 1 + b * t + p * t ^ 2
    let discriminant : ℝ := b ^ 2 - 4 * p
    let normalized : ℂ → ℂ := fun z =>
      z ^ 2 + ((b / Real.sqrt p : ℝ) : ℂ) * z + 1
    0 < discriminant ∧
      (∃ r₁ r₂ : ℝ,
        r₁ ≠ r₂ ∧
          numerator r₁ = 0 ∧
          numerator r₂ = 0 ∧
          normalized ((Real.sqrt p * r₁ : ℝ) : ℂ) = 0 ∧
          normalized ((Real.sqrt p * r₂ : ℝ) : ℂ) = 0) ∧
      ¬ ∃ z₁ z₂ : ℂ,
        z₁ ≠ z₂ ∧
          normalized z₁ = 0 ∧
          normalized z₂ = 0 ∧
          ‖z₁‖ = 1 ∧
          ‖z₂‖ = 1

end MathlibPlus.Open.ResearchFormalization.R0237.Claim19109
