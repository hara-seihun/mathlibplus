import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The deformed exponential's pantograph equation, with the defining infinite
series inlined and the source range `0 < q < 1` retained. -/
noncomputable def pantographDifferentialEquation_claim9539 : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    let E : ℝ → ℝ := fun x ↦
      ∑' k : ℕ,
        q ^ (Nat.choose k 2) * x ^ k / (Nat.factorial k : ℝ)
    (∀ x : ℝ, HasDerivAt E (E (q * x)) x) ∧ E 0 = 1

end MathlibPlus.Open.Analysis
