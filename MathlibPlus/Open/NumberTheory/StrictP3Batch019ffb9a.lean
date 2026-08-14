import Mathlib

namespace MathlibPlus.Open.NumberTheory.NewResearch2Batch

/-- 24478: the strict one-exterior p₃ lower bound, including the support
parameter r and its stated interval. -/
def strictOneExteriorP3LowerBound_24478 : Prop :=
  ∀ (S p₂ p₃ : ℕ),
    S > 4 → 16 < p₂ → p₂ < 4 * S →
      let r : ℚ := (4 * S - p₂ : ℚ) / (S - 4 : ℚ)
      0 < r ∧ r < 4 ∧
        (p₃ : ℚ) >
          ((p₂ : ℚ) ^ 2 - 32 * p₂ + 64 * S) / (S - 4 : ℚ)

end MathlibPlus.Open.NumberTheory.NewResearch2Batch
