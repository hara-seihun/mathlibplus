import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0241.Claim19134

/-- The shifted two-parameter recurrence is exposed rather than replaced by
its boundary arithmetic: the explicit positive sequence has coefficients
`a=b=1+β`, and the boundary-compatible product is exactly `β^2`, hence is
nonzero for every positive `β`. -/
def boundaryConditionInstability : Prop :=
  ∀ (β t₀ : ℝ),
    0 < β →
    0 < t₀ →
    let a : ℝ := 1 + β
    let b : ℝ := 1 + β
    let t : ℕ → ℝ := fun n =>
      t₀ * ∏ k ∈ Finset.range n,
        (((k : ℝ) + a) * ((k : ℝ) + b))⁻¹
    t 0 = t₀ ∧
      (∀ n : ℕ,
        t (n + 1) =
          t n * (((n : ℝ) + a) * ((n : ℝ) + b))⁻¹) ∧
      (∀ n : ℕ, 0 < t n) ∧
      a = 1 + β ∧
      b = 1 + β ∧
      (∀ n : ℕ,
        (((n : ℝ) + a) * ((n : ℝ) + b))⁻¹ =
          ((n : ℝ) + 1 + β)⁻¹ ^ 2) ∧
      (a - 1) * (b - 1) = β ^ 2 ∧
      0 < (a - 1) * (b - 1) ∧
      (a - 1) * (b - 1) ≠ 0 ∧
      ¬ ((a - 1) * (b - 1) = 0)

end MathlibPlus.Open.ResearchFormalization.R0241.Claim19134
