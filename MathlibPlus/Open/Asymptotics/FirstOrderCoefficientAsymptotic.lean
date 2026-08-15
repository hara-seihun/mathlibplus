import Mathlib

namespace MathlibPlus.Open.Asymptotics

/-- First-order coefficient asymptotic from Claim 8785.

The positive-real inverse characterization is the reviewed representation of the
principal Lambert `W₀` branch supplied by Claim 8783. -/
def firstOrderCoefficientAsymptotic_claim8785 : Prop :=
  ∀ (W₀ : ℝ → ℝ),
    (∀ x : ℝ, 0 < x →
      0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) →
    ∀ κ : ℝ, 0 < κ →
      let a : ℕ → ℝ := fun j =>
        W₀ ((j : ℝ) / κ) / (4 * (j : ℝ))
      ∃ r : ℕ → ℝ,
        Asymptotics.IsLittleO Filter.atTop r (fun _ : ℕ => (1 : ℝ)) ∧
        (a =ᶠ[Filter.atTop] (fun j =>
          Real.log (j : ℝ) / (4 * (j : ℝ)) * (1 + r j))) ∧
        Asymptotics.IsEquivalent Filter.atTop a
          (fun j => Real.log (j : ℝ) / (4 * (j : ℝ)))

end MathlibPlus.Open.Asymptotics
