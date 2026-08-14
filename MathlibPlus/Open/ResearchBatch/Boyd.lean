import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchBatch.Boyd

def boydPolynomialA₁ : Polynomial ℂ :=
  Polynomial.X ^ 5 - 2 * Polynomial.X ^ 4 - Polynomial.X ^ 3 -
    Polynomial.X ^ 2 + Polynomial.X + 1

def boydPolynomialA₂ : Polynomial ℂ :=
  Polynomial.X ^ 5 - 2 * Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 -
    Polynomial.X ^ 2 + 2 * Polynomial.X + 1

def explicit_boyd_polynomials_and_ordered_pisot_roots : Prop :=
  ∃ θ₁ θ₂ : ℝ,
    (247 / 100 : ℝ) < θ₁ ∧ θ₁ < (248 / 100 : ℝ) ∧
    (274 / 100 : ℝ) < θ₂ ∧ θ₂ < (275 / 100 : ℝ) ∧
    (∀ z : ℂ,
      (‖z‖ > 1 ∧ Polynomial.eval z boydPolynomialA₁ = 0) ↔
        z = (θ₁ : ℂ)) ∧
    (∀ z : ℂ,
      (‖z‖ > 1 ∧ Polynomial.eval z boydPolynomialA₂ = 0) ↔
        z = (θ₂ : ℂ)) ∧
    θ₁ < θ₂

end MathlibPlus.Open.ResearchBatch.Boyd
