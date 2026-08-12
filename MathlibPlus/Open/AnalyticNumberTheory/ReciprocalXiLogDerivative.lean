import Mathlib

/-!
# Explicit logarithmic-derivative estimate for reciprocal xi

Scratch elaboration for admitted claim 427.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/-- For the standard completed Riemann xi function, the logarithmic derivative of
`Q(x) = log ξ(1/2+x)` obeys the packet's explicit bound on `[3, ∞)`.  The
explicit remainder used by the packet is also strictly positive there. -/
noncomputable def explicitLogDerivativeEstimate : Prop :=
  let xi : ℝ → ℝ := fun s =>
    ((1 / 2 : ℂ) * (s : ℂ) * ((s : ℂ) - 1) *
      Complex.cpow (Real.pi : ℂ) (-(s : ℂ) / 2) *
      Complex.Gamma ((s : ℂ) / 2) * riemannZeta (s : ℂ)).re
  let Q : ℝ → ℝ := fun x => Real.log (xi (1 / 2 + x))
  let R : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * Real.log ((2 * Real.pi * x) / (x + 1 / 2)) -
      1 / (2 * x + 1) - 1 / (x - 1 / 2)
  (∀ x : ℝ, 3 ≤ x → deriv Q x ≤ (1 / 2 : ℝ) * Real.log x) ∧
    ∀ x : ℝ, 3 ≤ x → 0 < R x

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
