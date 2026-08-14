import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The signed power Sobolev inequalities with the radial derivative correction. -/
def signedPowerSobolev : Prop :=
  ∀ (J : Set ℝ) (ℓ : ℝ) (Q : ℝ → ℂ) (k : ℕ),
    Set.OrdConnected J →
    0 < ℓ →
    volume J = ENNReal.ofReal ℓ →
    ContDiffOn ℝ 1 Q J →
    1 ≤ k →
    let A : ℝ := ∫ x in J, ‖Q x‖ ^ (2 * k)
    let D : ℝ :=
      (k : ℝ) ^ 2 *
        ∫ x in J, ‖Q x‖ ^ (2 * k - 2) * ‖derivWithin Q J x‖ ^ 2
    let K : ℝ :=
      (k : ℝ) *
        ∫ x in J,
          ‖Q x‖ ^ (2 * k - 2) *
            Complex.im (derivWithin Q J x * star (Q x))
    K ^ 2 ≤ A * D ∧
      (A > 0 → D - K ^ 2 / A ≥ 0) ∧
      sSup ((fun x : ℝ => ‖Q x‖ ^ (2 * k)) '' J) ≤
        A / ℓ + 2 * Real.sqrt (A * (D - K ^ 2 / A))

end MathlibPlus.Open.Analysis
