import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0252

open Set

/-- Claim 15011: the parameterized anti-Stokes transition rectangle, with the
fixed domains of the surrounding model retained in the registry proposition. -/
noncomputable def claim15011_antiStokesTransitionRectangle : Prop :=
  ∀ (k : ℕ) (α L y₀ y₁ δ : ℝ),
    1 ≤ k →
    0 < α →
    0 < L →
    0 < y₀ →
    y₀ < y₁ →
    y₁ < 1 / 2 →
    0 < δ →
    δ < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) →
    ∃ (T x₁ x₂ y_b y_t : ℝ) (R : Set ℂ),
      T = Real.rpow L ((1 : ℝ) / (2 * (k : ℝ))) ∧
        x₁ = Real.rpow (((5 / 2 : ℝ) - y₁) / α)
          ((1 : ℝ) / (2 * (k : ℝ))) * T ∧
        x₂ = Real.rpow (((5 / 2 : ℝ) - y₀) / α)
          ((1 : ℝ) / (2 * (k : ℝ))) * T ∧
        y_b = y₀ - 2 * δ ∧
        y_t = y₁ + 2 * δ ∧
        R = {z : ℂ | ∃ x y : ℝ,
          x ∈ Set.Icc x₁ x₂ ∧
            y ∈ Set.Icc y_b y_t ∧
            z = (x : ℂ) + Complex.I * (y : ℂ)}

end MathlibPlus.Open.ResearchFormalization.O0252
