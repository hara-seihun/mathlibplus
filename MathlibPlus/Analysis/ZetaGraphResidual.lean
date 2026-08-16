import Mathlib

namespace MathlibPlus.Analysis.ZetaGraphResidual

/-!
# Denominator-free zeta-graph residual

Formalization of admitted claim 3901 (source locator `C-0275`).  The source
requires a compact test set in the half-plane `Re s > 1`; those hypotheses are
explicit parameters rather than silently extending the construction to an
arbitrary set.
-/

/-- The supremum of the denominator-free Mellin residual
`|M_p(s) - ζ(s) M_q(s)|` on a compact right-half-plane test set. -/
noncomputable def denominatorFreeResidual
    (M_p M_q : ℂ → ℂ) (K : Set ℂ)
    (_hK : IsCompact K)
    (_hKhalf : K ⊆ {s : ℂ | 1 < s.re}) : ℝ :=
  sSup ((fun s : ℂ => ‖M_p s - riemannZeta s * M_q s‖) '' K)

end MathlibPlus.Analysis.ZetaGraphResidual
