import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffee1

/-- Claim 39098: the odd square-free Hall-kernel hypotheses and directed
nonresonance condition on its finite prime set. -/
def NonresonantOddSquareFreeHallKernel (m : ℕ) (P : Finset ℕ) : Prop :=
  m = ∏ p ∈ P, p ∧
    Odd m ∧
    Squarefree m ∧
    ¬ 3 ∣ m ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    (∀ ⦃p q : ℕ⦄, p ∈ P → q ∈ P → p ≠ q → ¬ p ∣ q - 1)

end MathlibPlus.Open.ResearchFormalization.Batch019ffee1
