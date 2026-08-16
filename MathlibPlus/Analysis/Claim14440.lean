import Mathlib

namespace MathlibPlus.Analysis.Claim14440

/-- The slope/margin in the physical four-sector notation.  The packet names
`P` and `N` and the parameters `h₁`, `h₂` but supplies no further carrier
construction, so those displayed activities are explicit function arguments. -/
def physicalFourSectorSlope_claim14440
    (P N : ℝ → ℝ) (h₁ h₂ : ℝ) : ℝ :=
  P h₁ - h₂ * N h₁

end MathlibPlus.Analysis.Claim14440
