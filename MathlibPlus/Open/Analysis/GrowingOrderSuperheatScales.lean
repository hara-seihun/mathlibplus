import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The growing-order multiplier and the three scales retain their complete
hypotheses and their exact real and complex carriers. -/
def growingOrderSuperheatScales : Prop :=
  ∀ (k : ℕ → ℕ) (α L ε : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 1 ≤ L n) →
    Filter.Tendsto ε Filter.atTop (nhds 0) →
    (∀ n, 0 < ε n) →
    ∃ (M : ℕ → ℂ → ℂ) (a S V : ℕ → ℝ),
      (∀ n z,
        M n z = Complex.exp (-((α n : ℂ) * z ^ (2 * k n)))) ∧
      (∀ n,
        a n = Real.rpow (α n) (1 / (2 * (k n : ℝ)))) ∧
      (∀ n,
        S n = Real.rpow (L n / α n) (1 / (2 * (k n : ℝ))) ∧
        S n = Real.rpow (L n) (1 / (2 * (k n : ℝ))) / a n) ∧
      (∀ n,
        V n =
          Real.rpow (Real.log ((ε n)⁻¹) / α n)
            (1 / (2 * (k n : ℝ))))

end MathlibPlus.Open.Analysis
