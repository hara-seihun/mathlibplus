import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0122Claim18102

/-- Claim 18102: the spectral parameter q places the Borel branch point at
-πx² whenever x is nonzero. -/
def claim18102 : Prop :=
  ∀ x : ℝ, x ≠ 0 →
    let q : ℝ := 1 / (Real.pi * x ^ 2); -1 / q = -Real.pi * x ^ 2

end MathlibPlus.Open.ResearchFormalization.R0122Claim18102
