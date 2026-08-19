import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim7595

/-- The even real entire Hadamard-product context of the base Bessel
transform, including the nonzero normalization at the origin. -/
def record20HadamardProduct (G : ℂ → ℂ) (τ : ℕ → ℝ) : Prop :=
  Function.Even G ∧
    (∀ x : ℝ, (G (x : ℂ)).im = 0) ∧
    Differentiable ℂ G ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ z : ℂ,
          ‖G z‖ ≤ C * Real.exp (Real.rpow ‖z‖ (1 + ε))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ C : ℝ, 0 < C →
      ∃ z : ℂ,
        C * Real.exp (Real.rpow ‖z‖ (1 - ε)) < ‖G z‖) ∧
    (∀ j : ℕ, 0 < τ j) ∧
    (∀ w : ℂ,
      G w = 0 ↔
        ∃ j : ℕ, w = (τ j : ℂ) ∨ w = (-(τ j) : ℂ)) ∧
    Summable (fun j : ℕ => ((τ j) ^ 2)⁻¹) ∧
    (∀ w : ℂ,
      G w = G 0 * ∏' j : ℕ, (1 - w ^ 2 / (τ j : ℂ) ^ 2)) ∧
    G 0 ≠ 0 ∧
    0 < (G 0).re ∧
    (G 0).im = 0

/-- Strict comparison of the two imaginary shifts for the Record 20
Hadamard product in the upper half-plane. -/
def strictShiftAverageModulusInequality : Prop :=
  ∀ (G : ℂ → ℂ) (τ : ℕ → ℝ) (α : ℝ) (z : ℂ),
    record20HadamardProduct G τ →
    0 < α →
    0 < z.im →
      ‖G (z + Complex.I * α)‖ >
        ‖G (z - Complex.I * α)‖

end MathlibPlus.Open.ResearchFormalization.Claim7595
