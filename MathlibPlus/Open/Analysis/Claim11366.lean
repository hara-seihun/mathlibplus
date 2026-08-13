import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The exact polar-phase reading of admitted claim 11366.  The real amplitude
`R` and phase `φ` are made explicit, and `κ₆` is universally quantified as the
pointwise scalar appearing in the curvature subtraction.  The differentiability
assumptions make each displayed derivative well-defined without adding any
analytic conclusion beyond the source statement.
-/
def movingPhaseModulusDecomposition_claim11366 : Prop :=
  ∀ (R φ : ℝ → ℝ) (F : ℝ → ℂ),
    (∀ x, F x = (R x : ℂ) * Complex.exp (Complex.I * (φ x : ℂ))) →
    (∀ x, F x ≠ 0) →
    ContDiff ℝ 2 R →
    ContDiff ℝ 2 φ →
    ContDiff ℝ 2 F →
    ∀ x,
      deriv R x / R x = (deriv F x / F x).re ∧
      deriv (deriv R) x / R x =
        (deriv (deriv F) x / F x).re + (deriv F x / F x).im ^ 2 ∧
      deriv φ x = (deriv F x / F x).im ∧
      ∀ κ₆ : ℝ,
        deriv (deriv R) x / R x - κ₆ =
          ((deriv (deriv F) x / F x).re - κ₆) + (deriv φ x) ^ 2

end MathlibPlus.Open.Analysis
