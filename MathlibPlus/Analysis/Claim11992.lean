import Mathlib

namespace MathlibPlus.Analysis.Claim11992

/-- Exact exponential-moment optimization and the associated sequence scales from
claim 11992.  The supremum is represented by `sSup` of the values attained on
nonnegative real inputs; all powers with real exponents use `Real.rpow`. -/
noncomputable def exactSuperheatMomentOptimizationAndScales_claim11992 : Prop :=
  (∀ (α : ℝ) (k r : ℕ), 0 < α → 0 < k → 0 < r →
    sSup {y : ℝ | ∃ t : ℝ, 0 ≤ t ∧
      y = t ^ (2 * r) * Real.exp (-α * t ^ (2 * k))} =
      Real.rpow ((r : ℝ) / ((k : ℝ) * α * Real.exp 1))
        ((r : ℝ) / (k : ℝ))) ∧
  ∀ (k : ℕ → ℕ) (α L : ℕ → ℝ),
    Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ n, 0 < k n) →
    (∀ n, 0 < α n) →
    (∀ n, 1 ≤ L n) →
    let a : ℕ → ℝ := fun n =>
      Real.rpow (α n) (1 / (2 * (k n : ℝ)))
    let S : ℕ → ℝ := fun n =>
      Real.rpow (L n / α n) (1 / (2 * (k n : ℝ)))
    (∀ n, S n =
      Real.rpow (L n) (1 / (2 * (k n : ℝ))) / a n) ∧
    (∀ n,
      Real.rpow (L n / ((k n : ℝ) * α n * Real.exp 1))
          (1 / (2 * (k n : ℝ))) =
        Real.rpow ((k n : ℝ) * Real.exp 1)
          (-1 / (2 * (k n : ℝ))) * S n) ∧
    Filter.Tendsto
      (fun n => Real.rpow ((k n : ℝ) * Real.exp 1)
        (-1 / (2 * (k n : ℝ))))
      Filter.atTop (nhds 1)

end MathlibPlus.Analysis.Claim11992
