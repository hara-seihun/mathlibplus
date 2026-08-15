import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.ScalarIteration

noncomputable section
open scoped BigOperators

/-- The scalar recurrence has a factorial lower bound, including the explicit
    parity split of its `t = 2` coefficient. -/
def independentScalarIterationRemainsFactorial : Prop :=
  ∃ V : ℕ → ℝ,
    V 1 = 1 ∧
      V 2 = 1 ∧
      (∀ n : ℕ, 3 ≤ n →
        V n =
          1 + Finset.sum (Finset.Icc 2 (n - 1)) (fun t =>
            ((Nat.choose n t : ℝ) /
                ((n / t : ℕ) : ℝ)) * V (n - t + 1))) ∧
      (∀ n : ℕ, 3 ≤ n →
        ((Nat.choose n 2 : ℝ) /
            ((n / 2 : ℕ) : ℝ)) =
          if Even n then ((n - 1 : ℕ) : ℝ) else (n : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n →
        V n ≥ ((n - 1 : ℕ) : ℝ) * V (n - 1)) ∧
      (∀ n : ℕ, 1 ≤ n →
        V n ≥ (Nat.factorial (n - 1) : ℝ))

end

end MathlibPlus.Open.FormalizationBatch.ScalarIteration
