import Mathlib

/-!
# Gamma–Dini transition normalization

This file formalizes the two exact definitions in Record 1 of legacy packet
`C-0174`. The packet uses them on `1/2 ≤ η < 3/2`; the formulas themselves are
total Lean definitions. No later asymptotic or selector claim is included here.
-/

namespace MathlibPlus.GammaDiniTransition

/-- The transition scale `τ_η = (4/π)(5/2 - η)` from packet `C-0174`. -/
noncomputable def transitionScale (η : ℝ) : ℝ :=
  (4 / Real.pi) * ((5 : ℝ) / 2 - η)

/-- The phase-normalized transform
`B_{λ,η}(t) = 2 λ^{-η} exp(i t log λ) F_λ(t + iη)` from packet `C-0174`. -/
noncomputable def phaseNormalizedTransform
    (F : ℝ → ℂ → ℂ) (lambda η t : ℝ) : ℂ :=
  ((2 * lambda ^ (-η) : ℝ) : ℂ) *
    Complex.exp (Complex.I * t * Real.log lambda) *
    F lambda (t + Complex.I * η)

end MathlibPlus.GammaDiniTransition
