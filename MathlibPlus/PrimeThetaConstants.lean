import Mathlib

/-!
# Explicit Chebyshev-theta envelope constants

Exact rational arithmetic extracted from legacy packet `C-0047`.  These results
certify the packet's displayed constant and its numerical improvement only; the
analytic theta bounds and finite table envelope are separate statements.
-/

namespace MathlibPlus.PrimeThetaConstants

/-- The exact rational coefficient used by the packet's rounded FKS theta-table
envelope. -/
noncomputable def thetaLogCubeEnvelopeConstant : ℝ :=
  28681317 / 2000000000

/-- Both displayed forms of the exact theta-table envelope coefficient. -/
theorem thetaLogCubeEnvelopeConstant_value :
    thetaLogCubeEnvelopeConstant = 0.0143406585 ∧
      thetaLogCubeEnvelopeConstant = 1.5485e-12 * 2100 ^ 3 := by
  norm_num [thetaLogCubeEnvelopeConstant]

/-- Exact arithmetic comparison with the previously published coefficient. -/
theorem thetaLogCubeEnvelopeConstant_improves :
    thetaLogCubeEnvelopeConstant < 0.024334 ∧
      0.024334 - thetaLogCubeEnvelopeConstant = 0.0099933415 ∧
      1.6968 < 0.024334 / thetaLogCubeEnvelopeConstant := by
  norm_num [thetaLogCubeEnvelopeConstant]

end MathlibPlus.PrimeThetaConstants
