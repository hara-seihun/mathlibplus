import Mathlib

namespace MathlibPlus.Open.Analysis.ComplexSuperheat

/-- Claim 3105: uniform real-part expansion for fixed positive `k` and a fixed
real bound on `y`. The lower bound `k ≥ 1` is explicit because the displayed
error exponent is `2k - 2`. -/
def realPartExpansion : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℝ, 0 ≤ Y →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X : ℝ, 1 ≤ X ∧
      ∀ x y : ℝ, X ≤ x → |y| ≤ Y →
        |(((x : ℂ) + (y : ℂ) * Complex.I) ^ (2 * k)).re - x ^ (2 * k)| ≤
          C * x ^ (2 * k - 2)

end MathlibPlus.Open.Analysis.ComplexSuperheat
