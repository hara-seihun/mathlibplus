import Mathlib

namespace MathlibPlus.Open.Analysis.Entire

/-- Symmetric imaginary translation contracts a finite zero strip for a
nonconstant even real entire function of order strictly below two.

The order hypothesis is written in its standard growth-bound form: the function
has a global `exp (C * (‖z‖ ^ p + 1))` bound for some `p < 2`.
-/
def symmetricImaginaryShiftStripContraction : Prop :=
  ∀ (F : ℂ → ℂ),
    Differentiable ℂ F →
    (∃ z w : ℂ, F z ≠ F w) →
    (∀ z : ℂ, F (-z) = F z) →
    (∀ x : ℝ, (F (x : ℂ)).im = 0) →
    (∃ p C : ℝ, 0 ≤ p ∧ p < 2 ∧ 0 < C ∧
      ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (Real.rpow ‖z‖ p + 1))) →
    ∀ (Δ : ℝ), 0 ≤ Δ →
      (∀ ρ : ℂ, F ρ = 0 → |ρ.im| ≤ Δ) →
      ∀ (a : ℝ), 0 ≤ a →
        ∀ z : ℂ,
          F (z + Complex.I * a) + F (z - Complex.I * a) = 0 →
          |z.im| ≤ Real.sqrt (max (Δ ^ 2 - a ^ 2) 0)

end MathlibPlus.Open.Analysis.Entire
