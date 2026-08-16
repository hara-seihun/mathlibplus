import Mathlib

namespace MathlibPlus.Open.Analysis

/-- A nondegenerate locally uniform multiplier limit forces the root scale to
vanish and the reduced core scale to diverge. -/
def transferableMultiplierLimitsForceCoreDivergence : Prop :=
  ∀ (k : ℕ → ℕ) (α L : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 1 ≤ L n) →
    let a : ℕ → ℝ := fun n =>
      Real.rpow (α n) (1 / (2 * (k n : ℝ)))
    let S : ℕ → ℝ := fun n =>
      Real.rpow (L n / α n) (1 / (2 * (k n : ℝ)))
    let M : ℕ → ℂ → ℂ := fun n z =>
      Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))
    (∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      F 0 ≠ 0 ∧
      (∀ R : ℝ, 0 < R →
        ∀ δ : ℝ, 0 < δ →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ z : ℂ, ‖z‖ ≤ R → ‖M n z - F z‖ < δ)) →
    Filter.Tendsto a Filter.atTop (nhds 0) ∧
    (∀ n, (a n)⁻¹ ≤ S n) ∧
    Filter.Tendsto S Filter.atTop Filter.atTop

end MathlibPlus.Open.Analysis
