import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Relative deheating on every fixed positive radius is equivalent to an
unbounded visibility radius, including the bounded-subsequence obstruction and
its converse logarithmic estimate. -/
def relativeDeheatingVisibilityEquivalence_claim11987 : Prop :=
  ∀ (k : ℕ → ℕ) (α ε : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 0 < ε n) →
    Filter.Tendsto ε Filter.atTop (nhds 0) →
    let E : ℕ → ℝ := fun n => Real.log ((ε n)⁻¹)
    let V : ℕ → ℝ := fun n =>
      Real.rpow (E n / α n) (1 / (2 * (k n : ℝ)))
    let H : ℝ → ℕ → ℝ := fun R n =>
      Real.log (ε n * Real.exp (α n * R ^ (2 * k n)))
    let D : ℝ → ℕ → ℝ := fun R n =>
      E n * ((R / V n) ^ (2 * k n) - 1)
    ((∀ R : ℝ, 0 < R →
        Filter.Tendsto
          (fun n => ε n * Real.exp (α n * R ^ (2 * k n)))
          Filter.atTop (nhds 0)) ↔
      Filter.Tendsto V Filter.atTop Filter.atTop) ∧
    (∀ R : ℝ, 0 < R →
      ∀ᶠ n in Filter.atTop, H R n = D R n) ∧
    (∀ B R : ℝ, 0 < B → B < R →
      ∀ (φ : ℕ → ℕ),
        StrictMono φ →
        Filter.Tendsto φ Filter.atTop Filter.atTop →
        (∀ n, V (φ n) ≤ B) →
        (∀ᶠ n in Filter.atTop,
          H R (φ n) = D R (φ n)) ∧
        Filter.Tendsto (fun n => H R (φ n))
          Filter.atTop Filter.atTop) ∧
    (Filter.Tendsto V Filter.atTop Filter.atTop →
      ∀ R : ℝ, 0 < R →
        (∀ᶠ n in Filter.atTop,
          (R / V n) ^ (2 * k n) ≤ 1 / 2 ∧
            D R n ≤ -E n / 2) ∧
        Filter.Tendsto E Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => D R n)
          Filter.atTop Filter.atBot ∧
        Filter.Tendsto (fun n => H R n)
          Filter.atTop Filter.atBot)

end MathlibPlus.Open.Analysis
