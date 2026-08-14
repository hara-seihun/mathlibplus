import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch.FrontierArithmetic

/-- The recurrence and its factorial-product form are equivalent. -/
def claim59834_recurrenceProductEquivalence (m : ℕ → ℚ) : Prop :=
  (m 2 = (1 : ℚ) / 2 ∧
      ∀ n : ℕ,
        m (n + 3) =
          2 * (Nat.factorial (n + 2) : ℚ) * m (n + 2)) ↔
    (m 2 = (1 : ℚ) / 2 ∧
      ∀ n : ℕ,
        m (n + 3) =
          (2 : ℚ) ^ n *
            Finset.prod (Finset.range (n + 1)) (fun j =>
              (Nat.factorial (j + 2) : ℚ)))

/-- The fixed terminal values leave the parameter Lambda unbounded above. -/
def claim59835_unboundedTerminalParameter : Prop :=
  ∀ C : ℝ, ∃ Λ t y : ℝ,
    t = (1579 : ℝ) / 10000 ∧
      y = (1 : ℝ) / 10 ∧
      t + y ^ 2 / 2 = (1629 : ℝ) / 10000 ∧
      C < Λ

end MathlibPlus.Open.ResearchFormalizationBatch.FrontierArithmetic
