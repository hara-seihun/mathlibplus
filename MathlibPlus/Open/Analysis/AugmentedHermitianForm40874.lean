import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40874: the radial energy has the augmented Hermitian Gram form for
F₀, F₁, and F₂, and the current has its symmetric conjugate expression. -/
def augmentedHermitianForm_claim40874 : Prop :=
  ∀ (a b : ℝ) (Q : ℝ → ℂ) (k : ℕ),
    a ≤ b →
    2 ≤ k →
    ContDiff ℝ 1 Q →
    let F₀ : ℝ → ℂ := fun u => Q u ^ k
    let F₁ : ℝ → ℂ := fun u => Q u ^ (k - 1) * deriv Q u
    let F₂ : ℝ → ℂ := fun u => Q u ^ (k - 2) * (deriv Q u) ^ 2
    let Hk : ℝ → ℂ := fun u =>
      Q u ^ (k - 2) *
        (Complex.re (deriv Q u * star (Q u)) : ℂ)
    (∫ u in a..b, ‖deriv (fun t : ℝ => ‖Q t‖ ^ k) u‖ ^ 2 =
        (k : ℝ) ^ 2 * ∫ u in a..b, ‖Hk u‖ ^ 2) ∧
      (∫ u in a..b, ‖deriv (fun t : ℝ => ‖Q t‖ ^ k) u‖ ^ 2 =
        ((k : ℝ) ^ 2 / 2) *
          ((∫ u in a..b, ‖F₁ u‖ ^ 2) +
            ∫ u in a..b, Complex.re (F₂ u * star (F₀ u)))) ∧
      (∀ u : ℝ,
        Hk u =
          (Q u ^ (k - 2) * deriv Q u * star (Q u) +
            Q u ^ (k - 1) * star (deriv Q u)) / 2)

end MathlibPlus.Open.Analysis
