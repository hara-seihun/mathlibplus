import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Critical-strip bounds on the transverse parameter q. -/
def criticalStripBoundsOnQ : Prop :=
  ∀ (x δ γ : ℝ),
    0 < γ →
    x ≥ (1 / 4 : ℝ) →
    |δ| ≤ (1 / 2 : ℝ) →
    let d : ℝ := x + γ ^ 2
    let q : ℂ :=
      ((δ : ℂ) ^ 2 + 2 * Complex.I * (δ : ℂ) * (γ : ℂ)) / (d : ℂ)
    let β : ℝ := Real.sqrt (γ ^ 2 + (1 / 16 : ℝ)) / γ ^ 2
    Complex.re q ≤ 1 / (4 * γ ^ 2) ∧ ‖q‖ ≤ β

end MathlibPlus.Open.Analysis
