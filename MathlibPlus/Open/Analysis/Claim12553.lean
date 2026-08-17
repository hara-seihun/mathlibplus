import MathlibPlus.Open.Analysis.AppellCurrents

namespace MathlibPlus.Open.Analysis.AppellCurrents.Claim12553

noncomputable section

private def nonScalarDerivativeCoefficientsCancel
    (p γ : ℝ) (a A D : ℝ → ℝ) (B : ℝ → ℂ) : Prop :=
  ∀ x,
    deriv A x + 2 * (B x).re = 0 ∧
      ((A x : ℂ) * star (gaugedPotential p γ a x) +
          deriv B x + (D x : ℂ) = 0) ∧
      ((A x : ℂ) * gaugedPotential p γ a x +
          deriv (fun t => star (B t)) x + (D x : ℂ) = 0)

private def singleModeNormalForm
    (p γ : ℝ) (a A D : ℝ → ℝ) (B : ℝ → ℂ)
    (F : ℝ → ℝ) : Prop :=
  (∀ x,
    B x =
      (((-(deriv A x) : ℝ) : ℂ) +
          Complex.I * ((γ * F x : ℝ) : ℂ)) / (2 : ℂ)) ∧
  (∀ x, deriv F x = (p - a x) * A x) ∧
  (∀ x,
    D x = deriv (deriv A) x / 2 -
      A x * (gaugedPotential p γ a x).re)

/-- The coefficient-level normal form for every local Hermitian quadratic
current after the gauged equation has been substituted. -/
def completeSingleModeHermitianCurrentNormalForm : Prop :=
  ∀ (p γ : ℝ) (φ a : ℝ → ℝ) (y : ℝ → ℂ)
    (A D : ℝ → ℝ) (B : ℝ → ℂ),
    γ ≠ 0 →
    (∀ x, a x = deriv φ x) →
    (∀ x, deriv (deriv y) x =
      gaugedPotential p γ a x * y x) →
    (nonScalarDerivativeCoefficientsCancel p γ a A D B →
      ∃ F : ℝ → ℝ, singleModeNormalForm p γ a A D B F) ∧
    (∀ F : ℝ → ℝ,
      singleModeNormalForm p γ a A D B F →
        nonScalarDerivativeCoefficientsCancel p γ a A D B)

end

end MathlibPlus.Open.Analysis.AppellCurrents.Claim12553
