import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Relative-error visibility must diverge, with the exact logarithmic
obstruction exposed for every bounded subsequence. -/
def necessaryDivergenceOfRelativeErrorVisibility : Prop :=
  ∀ (k : ℕ → ℕ) (α ε : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 0 < ε n) →
    Filter.Tendsto ε Filter.atTop (nhds 0) →
    let E : ℕ → ℝ := fun n => Real.log ((ε n)⁻¹)
    let V : ℕ → ℝ := fun n =>
      Real.rpow (E n / α n) (1 / (2 * (k n : ℝ)))
    (∀ (B R : ℝ), 0 < B → B < R →
      ∀ (φ : ℕ → ℕ), StrictMono φ →
        Filter.Tendsto φ Filter.atTop Filter.atTop →
        (∀ n, V (φ n) ≤ B) →
        let H : ℕ → ℝ := fun n =>
          Real.log (ε n * Real.exp (α n * R ^ (2 * k n)))
        (∀ᶠ n in Filter.atTop,
          H (φ n) =
            E (φ n) *
              ((R / V (φ n)) ^ (2 * k (φ n)) - 1)) ∧
        Filter.Tendsto (fun n => H (φ n)) Filter.atTop Filter.atTop) ∧
    ((∀ R : ℝ, 0 < R →
        Filter.Tendsto
          (fun n => ε n * Real.exp (α n * R ^ (2 * k n)))
          Filter.atTop (nhds 0)) →
      Filter.Tendsto V Filter.atTop Filter.atTop)

end MathlibPlus.Open.Analysis
