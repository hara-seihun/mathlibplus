import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim1330

/-- The strict prime-counting inequality on the complete real half-line. -/
noncomputable def validFrom : ℝ → ℝ → Prop := fun c X =>
  ∀ x : ℝ, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - c / Real.log x)

/-- A natural start is least exactly when it is valid and every smaller natural
start fails the same half-line predicate. -/
noncomputable def leastIntegerStart : ℝ → ℕ → Prop := fun c N =>
  validFrom c (N : ℝ) ∧
    ∀ M : ℕ, M < N → ¬ validFrom c (M : ℝ)

end MathlibPlus.Open.ResearchFormalization.Claim1330
