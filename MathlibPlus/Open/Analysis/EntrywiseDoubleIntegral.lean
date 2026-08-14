import Mathlib

open scoped BigOperators

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Entrywise double-integral identity for the completed Bezout matrix. -/
def entrywiseDoubleIntegralIdentity : Prop :=
  ∀ (μ : Measure ℝ) (N : ℕ) (i j : ℕ),
    i < N → j < N →
      let h : ℕ → ℝ :=
        fun n =>
          (∫ x, x ^ n ∂(μ.restrict (Set.Ici (0 : ℝ)))) /
            ((Nat.factorial (2 * n) : ℕ) : ℝ)
      let C : ℕ → ℕ → ℝ :=
        fun p q =>
          ∑ a ∈ Finset.range (min p q + 1),
            ((p + q + 1 - 2 * a : ℕ) : ℝ) *
              h a * h (p + q + 1 - a)
      let κ : ℕ → ℕ → ℝ → ℝ → ℝ :=
        fun p q x y =>
          (1 / 2 : ℝ) *
            ∑ a ∈ Finset.range (min p q + 1),
              (((p + q + 1 - 2 * a : ℕ) : ℝ) /
                (((Nat.factorial (2 * a) : ℕ) : ℝ) *
                  ((Nat.factorial (2 * (p + q + 1 - a)) : ℕ) : ℝ))) *
                (x ^ a * y ^ (p + q + 1 - a) +
                  x ^ (p + q + 1 - a) * y ^ a)
      C i j =
        ∫ x, (∫ y, κ i j x y ∂(μ.restrict (Set.Ici (0 : ℝ))))
          ∂(μ.restrict (Set.Ici (0 : ℝ)))

end MathlibPlus.Open.Analysis
