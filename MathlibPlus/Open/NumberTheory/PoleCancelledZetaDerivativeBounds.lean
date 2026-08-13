import Mathlib

/-!
# Pole-cancelled Riemann-zeta derivative bounds

Statement-fidelity formalizations of admitted claims 1397 and 1398.  The
claims use real-axis notation `ζ'(s)` without defining a separate real zeta
function; these declarations use the real part of the complex derivative of
Mathlib's `riemannZeta` at the real point `(s : ℂ)`.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Claim 1397: on `1 < s ≤ 1.1`, the pole-cancelled zeta derivative is
strictly greater than `3/50`. -/
def localAlzerKwongLowerBound_claim1397 : Prop :=
  ∀ s : ℝ, 1 < s → s ≤ (11 : ℝ) / 10 →
    (deriv riemannZeta (s : ℂ)).re + 1 / (s - 1) ^ 2 > (3 : ℝ) / 50

/-- Claim 1398: the pole-cancelled zeta derivative is positive for every real
`s > 1`, written in the equivalent derivative inequality from the source. -/
def globalPoleCancelledDerivativePositive_claim1398 : Prop :=
  ∀ s : ℝ, 1 < s →
    - (deriv riemannZeta (s : ℂ)).re < 1 / (s - 1) ^ 2

end MathlibPlus.Open.NumberTheory
