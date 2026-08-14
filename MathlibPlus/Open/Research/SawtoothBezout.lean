import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.SawtoothBezout

/-- The two-coordinate sawtooth carrier in Claim 17881. -/
def sawtoothCarrier (p y : ℝ) : ℝ × ℝ :=
  (Real.exp (-(1 - p) * y), Real.exp (-p * y))

def sawtoothCarrier_formula : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 / 2 →
    ∀ y : ℝ,
      sawtoothCarrier p y =
        (Real.exp (-(1 - p) * y), Real.exp (-p * y))

def anchoredBezoutMatrix
    (h₀ h₁ h₂ h₃ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![h₀ * h₁, 2 * h₀ * h₂;
     2 * h₀ * h₂, h₁ * h₂ + 3 * h₀ * h₃]

def anchoredBezoutSection_formula : Prop :=
  ∀ (h₀ h₁ h₂ h₃ : ℝ),
    anchoredBezoutMatrix h₀ h₁ h₂ h₃ =
      !![h₀ * h₁, 2 * h₀ * h₂;
         2 * h₀ * h₂, h₁ * h₂ + 3 * h₀ * h₃]

def ratioCoordinateDeterminantFactorization : Prop :=
  ∀ (h₀ h₁ h₂ h₃ : ℝ),
    h₀ ≠ 0 → h₁ ≠ 0 → h₂ ≠ 0 →
      Matrix.det (anchoredBezoutMatrix h₀ h₁ h₂ h₃) =
        h₀ ^ 4 * (h₁ / h₀) ^ 2 * (h₂ / h₁) *
          ((h₁ / h₀) - 4 * (h₂ / h₁) + 3 * (h₃ / h₂))

def discreteRatioCurvaturePositivityCriterion : Prop :=
  ∀ (h₀ h₁ h₂ h₃ : ℝ),
    0 < h₀ → 0 < h₁ / h₀ → 0 < h₂ / h₁ →
      let a := h₁ / h₀
      let b := h₂ / h₁
      let c := h₃ / h₂
      (Matrix.det (anchoredBezoutMatrix h₀ h₁ h₂ h₃) > 0 ↔
        a - 4 * b + 3 * c > 0) ∧
      ((a - 4 * b + 3 * c > 0) ↔ a - b > 3 * (b - c))

def quotientRatioCurvatureCriterion : Prop :=
  ∀ (h₀ h₁ h₂ h₃ : ℝ),
    0 < h₀ → 0 < h₁ / h₀ → 0 < h₂ / h₁ →
    h₃ / h₂ < h₂ / h₁ →
      let a := h₁ / h₀
      let b := h₂ / h₁
      let c := h₃ / h₂
      ((a - 4 * b + 3 * c > 0) ↔ (a - b) / (b - c) > 3)

end MathlibPlus.Open.Research.SawtoothBezout
