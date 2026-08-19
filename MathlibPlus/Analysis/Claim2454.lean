import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 2454: the displayed center/transverse coordinates have the stated
explicit inverse.  The source's geometric interpretation of the two
coordinates is retained in the exact coordinate carrier below.
-/
theorem centerTransverseCoordinateChange_claim2454 (α β : ℝ) :
    let u := α + (5 / Real.pi) * β
    let v := β
    α = u - (5 / Real.pi) * v ∧ β = v := by
  dsimp
  constructor <;> ring

end MathlibPlus.Analysis
