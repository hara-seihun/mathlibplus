import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.CycleIndex

noncomputable section

/-- Arbitrary finite colours at every positive cycle length, with normalized
positive mass, have the same exponential cycle partition function. -/
def claim_12744 : Prop :=
  ∀ (colours : ℕ → ℕ)
    (π : ∀ ℓ : ℕ, Fin (colours ℓ) → ℝ),
    (∀ ℓ : ℕ, (∀ c : Fin (colours ℓ), 0 < π ℓ c) ∧
      ∑ c : Fin (colours ℓ), π ℓ c = 1) →
      ∀ z : ℂ, ‖z‖ < 1 →
        (∏' ℓ : ℕ, ∏' c : Fin (colours ℓ),
          Complex.exp ((π ℓ c : ℂ) * z ^ (ℓ + 1) / (ℓ + 1))) =
          Complex.exp (∑' ℓ : ℕ, z ^ (ℓ + 1) / (ℓ + 1)) ∧
        Complex.exp (∑' ℓ : ℕ, z ^ (ℓ + 1) / (ℓ + 1)) = 1 / (1 - z)

end
end MathlibPlus.Open.NewResearch2.CycleIndex
