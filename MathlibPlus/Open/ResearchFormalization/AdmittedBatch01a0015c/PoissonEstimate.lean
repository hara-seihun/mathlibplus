import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- Claim 14142: the sum-integral estimate used for the higher channels. -/
def claim14142 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 ≤ x →
      (∑' n : ℕ,
        if 0 < n then
          ((n : ℝ)⁻¹) ^ 4 * Real.exp (-x / (2 * (n : ℝ) ^ 2))
        else 0) ≤ C * Real.rpow x (-3 / 2)

end MathlibPlus.Open.ResearchFormalization
