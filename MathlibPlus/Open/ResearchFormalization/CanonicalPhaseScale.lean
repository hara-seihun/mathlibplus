import Mathlib

namespace MathlibPlus.Open

/-- The gamma-phase scale supplied by the exact shifted-moments context. -/
noncomputable def canonicalPhaseScale (sigma t : ℝ) : ℝ :=
  (Real.log Real.pi -
      (Complex.digamma
        (6 + ((sigma : ℂ) - (t : ℂ) * Complex.I) / 2)).re) / 2

/-- The positive radius is the negative of the canonical phase scale. -/
noncomputable def canonicalPhaseRadius (sigma t : ℝ) : ℝ :=
  -canonicalPhaseScale sigma t

/--
Canonical phase scale is globally positive in the stated sense: throughout
`1/2 ≤ sigma ≤ 1`, its phase speed is negative and its opposite is bounded
below by the displayed digamma constant, which is positive.
-/
noncomputable def canonicalPhaseScaleGloballyPositive : Prop :=
  ∀ sigma t : ℝ,
    (1 / 2 : ℝ) ≤ sigma →
    sigma ≤ 1 →
      canonicalPhaseScale sigma t < 0 ∧
        canonicalPhaseRadius sigma t ≥
          ((Complex.digamma (25 / 4 : ℂ)).re - Real.log Real.pi) / 2 ∧
        0 < ((Complex.digamma (25 / 4 : ℂ)).re - Real.log Real.pi) / 2

end MathlibPlus.Open
