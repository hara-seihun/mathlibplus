import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.SingleEffectiveFaceLogDerivative15410

/-- The projective first-jet determinant of two complex fields. -/
noncomputable def projectiveDelta (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  S z * deriv B z - deriv S z * B z

/-- The exact one-effective-face logarithmic-derivative identity. -/
def claim15410_singleEffectiveFaceLogDerivative : Prop :=
  ∀ (L : ℝ) (corridor : Set ℂ)
    (Φ₀ Φ₁ a₀ a₁ ε S B : ℂ → ℂ),
    IsOpen corridor →
      (∀ z ∈ corridor,
        S z = Complex.exp (-(L : ℂ) * Φ₀ z) * a₀ z) →
      (∀ z ∈ corridor,
        B z = Complex.exp (-(L : ℂ) * Φ₁ z) * a₁ z * (1 + ε z)) →
      ∀ z ∈ corridor,
        (DifferentiableAt ℂ Φ₀ z ∧
          DifferentiableAt ℂ Φ₁ z ∧
          DifferentiableAt ℂ a₀ z ∧
          DifferentiableAt ℂ a₁ z ∧
          DifferentiableAt ℂ ε z ∧
          S z ≠ 0 ∧ B z ≠ 0 ∧
          a₀ z ≠ 0 ∧ a₁ z ≠ 0 ∧ 1 + ε z ≠ 0) →
          projectiveDelta S B z / (S z * B z) =
            -(L : ℂ) * (deriv Φ₁ z - deriv Φ₀ z) +
              deriv a₁ z / a₁ z - deriv a₀ z / a₀ z +
                deriv ε z / (1 + ε z)

end MathlibPlus.Open.ResearchFormalization.SingleEffectiveFaceLogDerivative15410
