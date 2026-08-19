import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.NoetherClaim14660

/-- Claim 14660: the numerical Noether inequality check for the pair
`(c₁², c₂) = (7, 17)` is the displayed chain. -/
def noetherInequalityAdmissibility_claim14660 : Prop :=
  let c₁sq : ℤ := 7
  let c₂ : ℤ := 17
  5 * c₁sq = 35 ∧
    (35 : ℤ) ≥ c₂ - 36 ∧
    c₂ - 36 = (17 : ℤ) - 36 ∧
    (17 : ℤ) - 36 = (-19 : ℤ)

end MathlibPlus.Open.ResearchFormalization.NoetherClaim14660
