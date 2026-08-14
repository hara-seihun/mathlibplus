import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The shift comparison associated with an even Hadamard product over paired real zeros. -/
def shiftAverageModulusInequality (G : ℂ → ℂ) (α : ℝ) (z : ℂ) : Prop :=
  (∃ τ : ℕ → ℝ,
    (∀ j : ℕ, τ j ≠ 0) ∧
    Summable (fun j : ℕ => (τ j)⁻¹ ^ 2) ∧
    Differentiable ℂ G ∧
    (∀ w : ℂ, G (-w) = G w) ∧
    (∀ x : ℝ, (G (x : ℂ)).im = 0) ∧
    (∀ w : ℂ,
      G w = 0 ↔ ∃ j : ℕ, w = (τ j : ℂ) ∨ w = (-(τ j) : ℂ)) ∧
    (∀ w : ℂ,
      G w = G 0 * ∏' j : ℕ, (1 - w ^ 2 / (τ j : ℂ) ^ 2)) ∧
    0 < (G 0).re ∧ (G 0).im = 0) →
  0 < α →
  0 < z.im →
  ‖G (z + Complex.I * α)‖ >
    ‖G (z - Complex.I * α)‖

end MathlibPlus.Open.Analysis
