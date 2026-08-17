import Mathlib
import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.Open.NewResearch2.LunaBatch.O0072

noncomputable section

/-- Scalar positivity of the exact centered de Branges kernel derivative is
already equivalent to the Riemann hypothesis. -/
def claim12803_scalarDiagonalRHCriterion : Prop :=
  let xi : ℂ → ℂ :=
    MathlibPlus.NumberTheory.CompletedZetaRadial.riemannXi
  let Xi : ℂ → ℂ := fun z =>
    xi ((1 / 2 : ℂ) + Complex.I * z)
  let E : ℝ → ℂ → ℂ := fun ω z =>
    Xi (z + Complex.I * (ω : ℂ))
  let Esharp : ℝ → ℂ → ℂ := fun ω z =>
    Xi (z - Complex.I * (ω : ℂ))
  let Kdiag : ℝ → ℂ → ℝ := fun ω z =>
    ((E ω z * starRingEnd ℂ (E ω z) -
          Esharp ω z * starRingEnd ℂ (Esharp ω z)) /
        (2 * (Real.pi : ℂ) * Complex.I *
          (starRingEnd ℂ z - z))).re
  let RH : Prop := ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2
  RH ↔
    ∀ z : ℂ, 0 < z.im →
      ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
        0 ≤ deriv (fun u : ℝ => Kdiag u z) ω

end

end MathlibPlus.Open.NewResearch2.LunaBatch.O0072
