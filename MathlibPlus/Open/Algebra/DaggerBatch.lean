import Mathlib

namespace MathlibPlus.Open.Algebra.Dagger

/-- The mixed second-trace contribution of a two-way off-diagonal coupling. -/
def daggerMixedContribution (x y : ℂ) : ℂ := x * y + y * x

/-- In the dagger case the mixed contribution is exactly `2 |x|²` and vanishes only at zero. -/
def daggerCouplingTraceClaim : Prop :=
  ∀ x : ℂ,
    daggerMixedContribution x (starRingEnd ℂ x) =
        ((2 * Complex.normSq x : ℝ) : ℂ) ∧
      (daggerMixedContribution x (starRingEnd ℂ x) = 0 ↔ x = 0) ∧
      (x ≠ 0 → daggerMixedContribution x (starRingEnd ℂ x) ≠ 0)

end MathlibPlus.Open.Algebra.Dagger
