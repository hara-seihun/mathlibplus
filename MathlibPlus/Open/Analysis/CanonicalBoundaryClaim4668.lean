import Mathlib

namespace MathlibPlus.Open.Analysis.CanonicalBoundaryClaim4668

/-- The affine polynomial at the canonical boundary `b = 1/2`, on the real
formal-power-series carrier used by the ambient series. -/
noncomputable def canonicalBoundaryPolynomial (C : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C (1 / 2 : ℝ) -
    (PowerSeries.X + PowerSeries.C (1 / 4 : ℝ)) * C

end MathlibPlus.Open.Analysis.CanonicalBoundaryClaim4668
