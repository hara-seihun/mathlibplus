import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.D0036

def affineCoefficientRelations
    (b : ℝ) (t : ℕ → ℝ) (hZero : ℝ → ℝ) (h : ℕ → ℝ) : Prop :=
  hZero b = b - (1 / 4 : ℝ) * t 0 ∧
    ∀ n : ℕ, 1 ≤ n → h n = t (n - 1) - (1 / 4 : ℝ) * t n

end MathlibPlus.Open.ResearchFormalization.D0036
