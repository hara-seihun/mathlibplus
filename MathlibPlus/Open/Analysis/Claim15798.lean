import Mathlib

namespace MathlibPlus.Analysis.Claim15798

/-- The folded-density kernel from admitted claim 15798. -/
noncomputable def foldedDensityKernel_claim15798 (x u : ℝ) : ℝ :=
  x * (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
    Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

end MathlibPlus.Analysis.Claim15798
