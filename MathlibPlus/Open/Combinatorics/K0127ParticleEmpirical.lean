import Mathlib

namespace MathlibPlus.Open.Combinatorics

open MeasureTheory

/-- The empirical law of an `n`-particle configuration. -/
def claim8921 : Prop :=
  ∀ (z : ℕ → ℕ → ℝ) (n : ℕ), 0 < n →
    ∀ (S : {S : Finset ℕ // S.card = n}),
    ∃ μ : MeasureTheory.Measure ℝ,
      MeasureTheory.IsProbabilityMeasure μ ∧
        μ = (n : ENNReal)⁻¹ • ∑ i : S.1, MeasureTheory.Measure.dirac (z n i.1)

end MathlibPlus.Open.Combinatorics
