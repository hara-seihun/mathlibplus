import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The beta factor used in the centered-quartet estimate. -/
def quartetBeta (u : ℝ) : ℝ :=
  Real.sqrt (u ^ 2 + (1 / 16 : ℝ)) / u ^ 2

/-- The factor `F_m(T) = (1 - beta(T))^(-(m+2))`. -/
def quartetF (m : ℕ) (T : ℝ) : ℝ :=
  (1 - quartetBeta T)⁻¹ ^ (m + 2)

/-- Taking real parts removes the linear transverse term in one quartet. -/
def oneQuartetDefectQuadratic : Prop :=
  ∀ (m : ℕ) (T γ x δ : ℝ),
    0 < γ →
    γ ≥ T →
    x ≥ (1 / 4 : ℝ) →
    |δ| ≤ (1 / 2 : ℝ) →
    let d : ℝ := x + γ ^ 2
    let z : ℝ := d⁻¹
    let p : ℂ := ((δ : ℂ) + (γ : ℂ) * Complex.I) ^ 2
    let w : ℂ := ((x : ℂ) - p)⁻¹
    4 * |(w ^ m).re - z ^ m| ≤
      ((m : ℝ) +
          2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ) * quartetF m T) *
        (γ⁻¹) ^ (2 * m + 2) +
      ((m : ℝ) * ((m + 1 : ℕ) : ℝ) / 8) * quartetF m T *
        (γ⁻¹) ^ (2 * m + 4)

end MathlibPlus.Open.Analysis
