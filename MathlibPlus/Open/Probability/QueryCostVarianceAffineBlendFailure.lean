import Mathlib

namespace MathlibPlus.Open.Probability

/-- The exact scalar profile no-go behind the fixed query-cost/variance affine
blend obstruction. The finite-law realizations are intentionally not encoded
in this arithmetic registry carrier. -/
def queryCostVarianceAffineBlendFailure : Prop :=
  let Φ : ℝ → ℝ → ℝ → ℝ := fun α C V => α * C + (1 - α) * C * V
  let budgetExcess : ℝ → ℝ := fun α => Φ α 2 0 - 2
  let literalDefect : ℝ → ℝ :=
    fun α => (1 / 2 : ℝ) + Φ α (1 / 2) (1 / 4) - Φ α 1 (1 / 2)
  let selectorDefect : ℝ := (3 / 4 : ℝ) + 3 / 2 - 2
  ∀ α : ℝ,
    budgetExcess α > 0 ∨
      (literalDefect α = (1 - α) / 8 ∧ literalDefect α > 0) ∨
        (α = 1 ∧ selectorDefect = 1 / 4 ∧ selectorDefect > 0)

end MathlibPlus.Open.Probability
