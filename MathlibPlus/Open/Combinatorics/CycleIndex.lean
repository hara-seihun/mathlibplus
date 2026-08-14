import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.CycleIndex

/-- Claim 12744: finite positive colors at each positive cycle length normalize the
cycle factors to the uncolored exponential cycle partition function. -/
def claim12744 : Prop :=
  ∀ (C : ℕ+ → Finset ℕ) (π : ℕ+ → ℕ → ℝ) (z : ℂ),
    (∀ ℓ c, c ∈ C ℓ → 0 < π ℓ c) →
    (∀ ℓ, Finset.sum (C ℓ) (fun c => π ℓ c) = 1) →
    ‖z‖ < 1 →
      (∏' ℓ : ℕ+, (Finset.prod (C ℓ) (fun c =>
        Complex.exp
          (((π ℓ c : ℂ) * z ^ (ℓ : ℕ)) / ((ℓ : ℕ) : ℂ))))) =
        Complex.exp (∑' ℓ : ℕ+, z ^ (ℓ : ℕ) / ((ℓ : ℕ) : ℂ)) ∧
      Complex.exp (∑' ℓ : ℕ+, z ^ (ℓ : ℕ) / ((ℓ : ℕ) : ℂ)) = 1 / (1 - z)

end MathlibPlus.Open.Combinatorics.CycleIndex
