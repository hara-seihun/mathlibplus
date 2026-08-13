import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.CriticalParameter

/-- Universal feasibility at every finite rank has only the critical value. -/
def claim15784 (feasible : ℕ → Set ℝ) : Prop :=
  ∀ τ : ℝ, (∀ n : ℕ, τ ∈ feasible n) → τ = 1

/-- The uniqueness implication does not supply existence or feasibility of one. -/
def claim15785 : Prop :=
  ¬ ∀ feasible : ℕ → Set ℝ,
    (∀ τ : ℝ, (∀ n : ℕ, τ ∈ feasible n) → τ = 1) →
      ∃ τ : ℝ, ∀ n : ℕ, τ ∈ feasible n

end MathlibPlus.Open.Analysis.CriticalParameter
