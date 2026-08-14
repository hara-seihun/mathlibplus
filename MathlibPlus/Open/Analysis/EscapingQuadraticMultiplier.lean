import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The quadratic multiplier family from admitted claim 42853. -/
noncomputable def escapingQuadraticMultiplier (R : ℝ) (z : ℂ) : ℂ :=
  1 + (z / (R : ℂ)) ^ 2

end MathlibPlus.Open.Analysis
