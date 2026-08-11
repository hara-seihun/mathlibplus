import Mathlib

/-!
# Order-two translation minors of the reciprocal completed-xi transform

This registry node records admitted claim 379. The completed xi function and the
Fourier normalization from claim 375 are inlined to keep the statement attached to
the literal reciprocal-xi kernel rather than to an arbitrary function.
-/

namespace MathlibPlus.Open.Analysis.ReciprocalXi

/-- Strictly ordered nodes give strictly positive order-two translation minors of
the reciprocal completed-xi transform; weakly ordered nodes give nonnegative minors.
Reality is stated explicitly because the Fourier integral is represented in `ℂ`. -/
noncomputable def strictOrderTwoTranslationMinors : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2) * riemannZeta s
  let X : ℝ → ℂ := fun x => xi ((1 / 2 + x : ℝ) : ℂ)
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) / X x
  let Lambda : ℝ → ℂ := fun t => F t / (2 * Real.pi : ℝ)
  (∀ x₁ x₂ y₁ y₂ : ℝ, x₁ < x₂ → y₁ < y₂ →
      let d := Lambda (x₁ - y₁) * Lambda (x₂ - y₂) -
        Lambda (x₁ - y₂) * Lambda (x₂ - y₁)
      d.im = 0 ∧ 0 < d.re) ∧
    (∀ x₁ x₂ y₁ y₂ : ℝ, x₁ ≤ x₂ → y₁ ≤ y₂ →
      let d := Lambda (x₁ - y₁) * Lambda (x₂ - y₂) -
        Lambda (x₁ - y₂) * Lambda (x₂ - y₁)
      d.im = 0 ∧ 0 ≤ d.re)

end MathlibPlus.Open.Analysis.ReciprocalXi
