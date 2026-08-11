import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The completed-zeta radial normalization

The completed Riemann xi function and the radial functions used by the
completed-zeta Loewner kernels.
-/

namespace MathlibPlus.NumberTheory.CompletedZetaRadial

open Complex Set

/-- The entire Riemann xi function, expressed using mathlib's pole-subtracted
entire completed zeta `completedRiemannZeta₀`.

Away from `0` and `1`, this is
`(s * (s - 1) * completedRiemannZeta s) / 2`; the displayed form also gives
the pole-cancelled endpoint values. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The completed xi function on the radial line `s = 1/2 + r`. -/
noncomputable def radialX (r : ℝ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + r)

/-- The logarithmic derivative `X'(r) / X(r)` of the completed radial
function.  `deriv` here is the real derivative of the complex-valued radial
restriction. -/
noncomputable def radialLogDerivative (r : ℝ) : ℂ :=
  deriv radialX r / radialX r

/-- The completed-zeta radial kernel `L(√x) / √x`, on its stated domain
`x ≥ 1/4`. -/
noncomputable def radialKernel (x : Set.Ici (1 / 4 : ℝ)) : ℂ :=
  radialLogDerivative (Real.sqrt x) / Real.sqrt x

end MathlibPlus.NumberTheory.CompletedZetaRadial
