import Mathlib

open scoped BigOperators Interval

namespace MathlibPlus.Open.Research

/-- Exact cumulative local-threshold formula for the Nicolas ratios along the
positive-indexed prime sequence. -/
def exactCumulativeLocalThresholdFormula : Prop :=
  ∀ (p : ℕ → ℕ) (T : ℕ → ℝ) (k₀ K : ℕ),
    p 1 = 2 →
    (∀ n : ℕ, 1 ≤ n → Nat.Prime (p n)) →
    (∀ {m n : ℕ}, 1 ≤ m → m < n → p m < p n) →
    (∀ q : ℕ, Nat.Prime q ↔ ∃ n : ℕ, 1 ≤ n ∧ p n = q) →
    (∀ q : ℕ, Nat.Prime q →
      0 < T q ∧
      Real.log (q : ℝ) =
        T q * (Real.exp (Real.log (T q) / ((q : ℝ) - 1)) - 1) ∧
      ∀ t : ℝ, 0 < t →
        Real.log (q : ℝ) =
          t * (Real.exp (Real.log t / ((q : ℝ) - 1)) - 1) →
        t = T q) →
    1 ≤ k₀ →
    k₀ < K →
    let N : ℕ → ℕ := fun k => Finset.prod (Finset.Icc 1 k) p
    let θ : ℕ → ℝ := fun k => Real.log (N k : ℝ)
    let u : ℕ → ℝ :=
      fun k =>
        (N k : ℝ) /
          ((Nat.totient (N k) : ℝ) * Real.log (Real.log (N k : ℝ)))
    Real.log (u K / u k₀) =
      Finset.sum (Finset.Ico k₀ K) (fun k =>
        ∫ v in (T (p (k + 1)))..(θ k),
          (1 / (v * Real.log v) -
            1 /
              ((v + Real.log (p (k + 1) : ℝ)) *
                Real.log (v + Real.log (p (k + 1) : ℝ)))))

end MathlibPlus.Open.Research
