import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 10209: the Laplace moment of every nonnegative integer monomial. -/
def laplaceMomentMonomial : Prop :=
  ∀ k : ℕ, ∀ s : ℝ, 0 < s →
    (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-s * t) * t ^ k) =
      (Nat.factorial k : ℝ) / s ^ (k + 1)

end

end MathlibPlus.Analysis
