import Mathlib

/-!
# Exact logarithmic derivative of the reciprocal-xi potential

This registry node records admitted claim 462. The source writes a quotient formula
without a domain. Here it is stated on the natural common domain of the displayed
factors; no assertion is made at removable singularities of the separated terms.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/-- For `Q(x) = log ξ(1/2+x)`, the completed-zeta product gives the displayed exact
logarithmic derivative wherever its separated Gamma and zeta logarithmic derivatives
are defined. -/
noncomputable def exactLogDerivative : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 / 2 : ℂ) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2) * riemannZeta s
  let realXi : ℝ → ℝ := fun x =>
    (xi (((1 / 2 : ℝ) + x : ℝ) : ℂ)).re
  let Q : ℝ → ℝ := fun x => Real.log (realXi x)
  ∀ x : ℝ,
    let s : ℝ := x + 1 / 2
    s ≠ 0 → s ≠ 1 →
      riemannZeta (s : ℂ) ≠ 0 → Complex.Gamma ((s / 2 : ℝ) : ℂ) ≠ 0 →
        deriv Q x =
          1 / s + 1 / (s - 1) - (1 / 2 : ℝ) * Real.log Real.pi +
            (1 / 2 : ℝ) * (Complex.digamma ((s / 2 : ℝ) : ℂ)).re +
            ((deriv riemannZeta (s : ℂ)) / riemannZeta (s : ℂ)).re

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
