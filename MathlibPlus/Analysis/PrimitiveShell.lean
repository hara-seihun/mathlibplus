import Mathlib

namespace MathlibPlus.Analysis.PrimitiveShell

/-- The first turning point used by the primitive shell. -/
noncomputable def firstTurningPoint : ℝ :=
  (1 / 2 : ℝ) * Real.log ((15 + Real.sqrt 105) / (8 * Real.pi))

end MathlibPlus.Analysis.PrimitiveShell
