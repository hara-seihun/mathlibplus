import Mathlib

namespace MathlibPlus.Analysis

/--
The ratio-preservation fragment of claim 11524.  A nonvanishing two-periodic
factor does not change a reciprocal two-step quotient.
-/
theorem positiveGauge_preserves_twoStepRatio_11524
    (X Q : ℂ → ℂ) (z : ℂ)
    (hX0 : X z ≠ 0) (hX2 : X (z + 2) ≠ 0)
    (hQ0 : Q z ≠ 0) (_hQ2 : Q (z + 2) ≠ 0)
    (hQper : Q (z + 2) = Q z) :
    (X (z + 2) * Q (z + 2)) / (X z * Q z) = X (z + 2) / X z := by
  rw [hQper]
  field_simp

end MathlibPlus.Analysis
