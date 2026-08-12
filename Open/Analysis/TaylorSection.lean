import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.TaylorSection

/--
Claim 17443.  “Taylor section” is expanded as the degree-`N` sum of the
iterated complex derivatives at zero, divided by factorials.  The supremum on
`|z| ≤ R` is expressed pointwise, and the source's standard positivity/type
conventions for `A` and `τ` are left visible in the exponential-type premise
rather than silently chosen.
-/
noncomputable def exponentialTypeTaylorErrorBound_claim17443 : Prop :=
  ∀ (F : ℂ → ℂ) (A τ : ℝ),
    Differentiable ℂ F →
    (∀ z : ℂ, ‖F z‖ ≤ A * Real.exp (τ * ‖z‖)) →
    ∀ (N : ℕ) (R : ℝ), 0 ≤ R →
      let taylorSection : ℕ → ℂ → ℂ := fun N z =>
        ∑ k ∈ Finset.range (N + 1),
          (iteratedDeriv k F 0 / (Nat.factorial k : ℂ)) * z ^ k
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖F z - taylorSection N z‖ ≤
          2 * A * Real.exp (2 * τ * R) / (2 : ℝ) ^ (N + 1)

end MathlibPlus.Open.Analysis.TaylorSection
