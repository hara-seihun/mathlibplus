import Mathlib

open MeasureTheory
open Set

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The two Lorentz slacks are the stated double integrals for a measure
supported on the nonnegative half-line, together with their nonnegativity. -/
def lorentzSlackDoubleIntegralFormulas : Prop :=
  ∀ (μ : Measure ℝ) (m : ℕ → ℝ),
    μ (Iio (0 : ℝ)) = 0 →
    (∀ j : ℕ, j ≤ 3 → m j = ∫ x : ℝ, x ^ j ∂μ) →
    let Δ₀ := m 0 * m 2 - (m 1) ^ 2
    let Δ₁ := m 1 * m 3 - (m 2) ^ 2
    Δ₀ = (1 / 2 : ℝ) *
        (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ)) ∧
      Δ₁ = (1 / 2 : ℝ) *
        (∫ p : ℝ × ℝ, p.1 * p.2 * (p.1 - p.2) ^ 2 ∂(μ.prod μ)) ∧
      0 ≤ Δ₀ ∧ 0 ≤ Δ₁

/-- The factorial-scaled moment-curve matrix associated with ordered rows and
columns. -/
noncomputable def weightedMomentCurveMatrix {r : ℕ} (x w : ℕ → ℝ)
    (rows cols : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    w (rows i) * x (rows i) ^ (cols j) /
      (Nat.factorial (2 * cols j) : ℝ)

/-- Strict total positivity for every finite ordered choice of rows and
columns of the factorial-scaled weighted moment curve. -/
def weightedMomentCurveStrictTotalPositivity : Prop :=
  ∀ (x w : ℕ → ℝ),
    StrictMono x →
    (∀ n : ℕ, 0 < x n) →
    (∀ n : ℕ, 0 < w n) →
    ∀ (r : ℕ) (rows cols : Fin r → ℕ),
      StrictMono rows →
      StrictMono cols →
      0 < Matrix.det (weightedMomentCurveMatrix x w rows cols)

end MathlibPlus.Open.ResearchFormalizationBatch
