import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The quadratic-form definition of positive definiteness for a complex function on `ℝ`. -/
def researchPositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    let q : ℂ := ∑ i, ∑ j, star (c i) * c j * f (x i - x j)
    0 ≤ q.re ∧ q.im = 0

/-- Positive-definite reciprocal rigidity, including its character and real-even conclusions. -/
def claim13926 : Prop :=
  ∀ (a : ℝ → ℂ),
    Continuous a →
    researchPositiveDefinite a →
    a 0 = 1 →
    (∀ x : ℝ, a x ≠ 0) →
    researchPositiveDefinite (fun x => (a x)⁻¹) →
    ((∀ x : ℝ, ‖a x‖ = 1) ∧
      (∃ lambda : ℝ, ∀ x : ℝ,
        a x = Complex.exp (Complex.I * ((lambda * x : ℝ) : ℂ))) ∧
      ((∀ x : ℝ, (a x).im = 0) →
        (∀ x : ℝ, a (-x) = a x) →
        ∀ x : ℝ, a x = 1))

end MathlibPlus.Open.ResearchFormalization
