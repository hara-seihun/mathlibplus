import Mathlib

namespace MathlibPlus.Open.Analysis

/-- In a fixed closed substrip, the visibility radius and the reduced core
scale are asymptotic, with the hidden positive constant factor exposed. -/
def fixedSubstripCoreVisibilityAsymptotics_claim11996 : Prop :=
  ∀ (k : ℕ → ℕ) (α L ε : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 1 ≤ L n) →
    (∀ n, 0 < ε n) →
    Filter.Tendsto ε Filter.atTop (nhds 0) →
    let E : ℕ → ℝ := fun n => Real.log ((ε n)⁻¹)
    let V : ℕ → ℝ := fun n =>
      Real.rpow (E n / α n) (1 / (2 * (k n : ℝ)))
    let S : ℕ → ℝ := fun n =>
      Real.rpow (L n / α n) (1 / (2 * (k n : ℝ)))
    (∃ lower upper : ℝ,
      0 < lower ∧
      0 < upper ∧
      (∀ᶠ n in Filter.atTop,
        lower * L n ≤ E n ∧ E n ≤ upper * L n)) →
      (∀ᶠ n in Filter.atTop,
        V n / S n =
          Real.rpow (E n / L n) (1 / (2 * (k n : ℝ)))) ∧
      Filter.Tendsto (fun n => V n / S n)
        Filter.atTop (nhds 1)

end MathlibPlus.Open.Analysis
