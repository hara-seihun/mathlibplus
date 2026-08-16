import Mathlib

namespace MathlibPlus.Open.Algebra

def rationalCubicUniqueDiscriminantWall : Prop :=
  let P₀ : Polynomial ℂ :=
    (Polynomial.X ^ 2 + Polynomial.C (1 : ℂ)) *
      (Polynomial.X - Polynomial.C (3 : ℂ))
  let P₁ : Polynomial ℂ :=
    (Polynomial.X + Polynomial.C (2 : ℂ)) *
      (Polynomial.X - Polynomial.C (1 : ℂ)) *
        (Polynomial.X - Polynomial.C (3 / 2 : ℂ))
  let P : ℝ → Polynomial ℂ := fun s =>
    ((1 - s : ℝ) : ℂ) • P₀ + (s : ℝ) • P₁
  let F : ℝ → ℂ → ℂ := fun s z => (P s).eval z
  let dF : ℝ → ℂ → ℂ := fun s z =>
    ((1 - s : ℝ) : ℂ) * (2 * z * (z - 3) + (z ^ 2 + 1)) +
      (s : ℝ) *
        ((z - 1) * (z - (3 / 2 : ℂ)) +
          (z + 2) * (z - (3 / 2 : ℂ)) + (z + 2) * (z - 1))
  let disc : ℝ → ℂ := fun s => Polynomial.discr (P s)
  let displayedDisc : ℝ → ℝ := fun s =>
    (-(1 : ℝ) / 16) *
      (3975 * s ^ 4 - 5232 * s ^ 3 + 13616 * s ^ 2 - 19200 * s + 6400)
  let displayedDiscDerivative : ℝ → ℝ := fun s =>
    (-(1 : ℝ) / 16) *
      (4 * 3975 * s ^ 3 - 3 * 5232 * s ^ 2 + 2 * 13616 * s - 19200)
  (∀ s : ℝ, disc s = (displayedDisc s : ℂ)) ∧
    F 0 Complex.I = 0 ∧ F 0 (-Complex.I) = 0 ∧ F 0 (3 : ℂ) = 0 ∧
    F 1 (-2 : ℂ) = 0 ∧ F 1 (1 : ℂ) = 0 ∧ F 1 (3 / 2 : ℂ) = 0 ∧
    ∃ s₀ : ℝ,
      0 < s₀ ∧ s₀ < 1 ∧
      displayedDisc s₀ = 0 ∧ displayedDiscDerivative s₀ ≠ 0 ∧
      46 / 97 < s₀ ∧ s₀ < 83 / 175 ∧
      (∀ s : ℝ, 0 < s → s < 1 → disc s = 0 → s = s₀) ∧
      (∀ s : ℝ, s₀ < s → s ≤ 1 → disc s ≠ 0) ∧
      (∃ r c : ℝ,
        2 < r ∧ r < 5 / 2 ∧ c < 0 ∧
          F s₀ (r : ℂ) = 0 ∧ dF s₀ (r : ℂ) ≠ 0 ∧
          F s₀ (c : ℂ) = 0 ∧ dF s₀ (c : ℂ) = 0 ∧
          ∀ z : ℂ, F s₀ z = 0 → z = (r : ℂ) ∨ z = (c : ℂ))

end MathlibPlus.Open.Algebra
