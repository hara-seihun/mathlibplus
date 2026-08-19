import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim35799

/-- The exact geometric-decay bounds through the initial cases. -/
def geometricDecayBounds_claim35799 : Prop :=
  (∀ k : ℕ, 5 ≤ k →
    (3 / 5 : ℝ) ^ k ≤ 1 / (2 * (k : ℝ))) ∧
    (3 / 5 : ℝ) ^ 2 < 1 / 2 ∧
    (3 / 5 : ℝ) ^ 3 < 1 / 4 ∧
    (3 / 5 : ℝ) ^ 4 < 1 / 4

end MathlibPlus.Open.ResearchFormalization.Claim35799
