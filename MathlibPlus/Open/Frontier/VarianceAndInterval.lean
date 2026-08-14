import Mathlib

namespace MathlibPlus.Open.Frontier

/-- The explicit finite-Rademacher-cube obstruction to a variance-only
Bellman supersolution. -/
def noContinuousVarianceOnlyBellmanSupersolution : Prop :=
  ¬ ∃ φ : ℝ → ℝ,
      ContinuousAt φ 0 ∧
      φ 0 = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        ∀ r : ℕ, 1 ≤ r → r ≤ n →
          φ ((r : ℝ) / (n : ℝ) ^ 2) ≥
            (r : ℝ) / (n : ℝ) ^ 2 +
              φ ((↑(r - 1) : ℝ) / (n : ℝ) ^ 2)

/-- The positive-null-scale endpoint construction, including its failure to
straddle one. -/
def pencilTauArbitraryPositiveNullScaleStraddlingObstruction : Prop :=
  ∀ (r : ℕ → ℝ),
    (∀ n, 0 < r n) →
    Filter.Tendsto r Filter.atTop (nhds 0) →
    ∃ (L U : ℕ → ℝ) (C : ℕ → Set ℝ),
      Filter.Tendsto L Filter.atTop (nhds 1) ∧
      Filter.Tendsto U Filter.atTop (nhds 1) ∧
      (∀ n, (L n - 1) / r n = 1) ∧
      (∀ n, (U n - 1) / r n = 2) ∧
      (∀ n, C n = Set.Icc (L n) (U n)) ∧
      (∀ n, (C n).Nonempty) ∧
      (∀ n, IsClosed (C n)) ∧
      (∀ n, ¬ (L n < 1 ∧ 1 < U n)) ∧
      (∀ n, 1 < L n)

end MathlibPlus.Open.Frontier
