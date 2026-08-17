import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Local-uniform convergence of the growing-order multiplier is equivalent to
vanishing root scale, with the constant-one entire limit. -/
def localUniformMultiplierConvergenceDichotomy_claim11985 : Prop :=
  ∀ (k : ℕ → ℕ) (α : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    ∀ (φ : ℕ → ℕ),
      StrictMono φ →
      Filter.Tendsto φ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun n => k (φ n)) Filter.atTop Filter.atTop →
      let M : ℕ → ℂ → ℂ := fun n z =>
        Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))
      let a : ℕ → ℝ := fun n =>
        Real.rpow (α n) (1 / (2 * (k n : ℝ)))
      let locallyUniform : (ℕ → ℂ → ℂ) → (ℂ → ℂ) → Prop :=
        fun Fseq F =>
          ∀ R : ℝ, 0 < R →
            ∀ δ : ℝ, 0 < δ →
              ∀ᶠ n in Filter.atTop,
                ∀ z : ℂ, ‖z‖ ≤ R → ‖Fseq n z - F z‖ < δ
      ((∃ F : ℂ → ℂ,
          Differentiable ℂ F ∧
            locallyUniform (fun n z => M (φ n) z) F) ↔
        Filter.Tendsto (fun n => a (φ n)) Filter.atTop (nhds 0)) ∧
        (∀ F : ℂ → ℂ,
          Differentiable ℂ F →
            locallyUniform (fun n z => M (φ n) z) F →
              ∀ z : ℂ, F z = 1)

end MathlibPlus.Open.Analysis
