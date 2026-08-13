import Mathlib

open Filter Asymptotics

namespace MathlibPlus.Open.Analysis

/-- Faithful registry node for the fixed-substrip visibility/core asymptotic.
The two-sided eventual bounds are the explicit Lean form of the two Theta
hypotheses; the source's zero geometry is not silently reconstructed. -/
def visibilityCoreAsymptoticEquivalence_claim11988 : Prop :=
  ∀ (epsilon L : ℕ → ℝ) (k : ℕ → ℕ) (S V c : ℕ → ℝ),
    (∀ᶠ n in atTop, 0 < epsilon n) →
    (∃ lower upper : ℝ,
      0 < lower ∧ 0 < upper ∧
        (∀ᶠ n in atTop,
          0 < L n ∧
          lower * L n ≤ Real.log ((epsilon n)⁻¹) ∧
          Real.log ((epsilon n)⁻¹) ≤ upper * L n)) →
    Tendsto k atTop atTop →
    (∃ lower upper : ℝ,
      0 < lower ∧ lower ≤ upper ∧
        (∀ᶠ n in atTop, lower ≤ c n ∧ c n ≤ upper)) →
    (∀ n,
      V n = c n ^ ((1 : ℝ) / (2 * (k n : ℝ))) * S n) →
    (∀ᶠ n in atTop, S n ≠ 0) →
    (fun n => V n) ~[atTop] (fun n => S n)

end MathlibPlus.Open.Analysis
