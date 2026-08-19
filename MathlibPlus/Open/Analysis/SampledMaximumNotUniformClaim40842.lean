import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40842: a finite proper sample below a budget does not by itself
certify a uniform bound on a continuous block. -/
def sampledMaximumBelowBudgetNotUniform_claim40842 : Prop :=
  ∃ (f : ℝ → ℝ) (I S : Set ℝ) (B : ℝ),
    Continuous f ∧
      S.Finite ∧
      S ⊆ I ∧
      (∃ x, x ∈ I ∧ x ∉ S) ∧
      (∀ x ∈ S, f x < B) ∧
      ¬ (∀ x ∈ I, f x < B)

end MathlibPlus.Open.Analysis
