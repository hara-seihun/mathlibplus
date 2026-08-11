import Mathlib

/-!
# Rigidity of the final Hankel boundary

Statement-fidelity formalization of admitted claim 148.  “Finite positive measure
supported on `[0, ∞)` with moments through degree five” is expressed by a finite
`Measure ℝ`, zero mass off `Set.Ici 0`, and integrability of every monomial of
degree at most five.  Support on `{0, z}` is expressed measure-theoretically, so
zero-mass points do not affect the statement.
-/

namespace MathlibPlus.Open.Analysis.Moment

open MeasureTheory Set
open scoped ENNReal

/-- Equality in the final shifted-Hankel minor forces all positive support onto one
point; for two positive atoms, the defect has the displayed exact factorization. -/
def rigidityOfFinalHankelBoundary : Prop :=
  (∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      μ ((Set.Ici (0 : ℝ))ᶜ) = 0 →
      (∀ k : ℕ, k ≤ 5 → Integrable (fun x : ℝ => x ^ k) μ) →
      let m : ℕ → ℝ := fun k => ∫ x : ℝ, x ^ k ∂μ
      m 3 * m 5 = (m 4) ^ 2 ↔
        ∃ z : ℝ, 0 ≤ z ∧ μ (({0, z} : Set ℝ)ᶜ) = 0) ∧
    ∀ w₁ w₂ z₁ z₂ : ℝ,
      0 < w₁ → 0 < w₂ → 0 < z₁ → 0 < z₂ →
      let m : ℕ → ℝ := fun k => w₁ * z₁ ^ k + w₂ * z₂ ^ k
      m 3 * m 5 - (m 4) ^ 2 =
        w₁ * w₂ * z₁ ^ 3 * z₂ ^ 3 * (z₁ - z₂) ^ 2

end MathlibPlus.Open.Analysis.Moment
