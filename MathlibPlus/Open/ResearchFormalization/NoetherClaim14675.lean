import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.NoetherClaim14675

/-- Claim 14675: the displayed Noether quotient for `(c₁², c₂) = (13, 11)`
is `2`, and the corresponding integer sum is divisible by `12`. -/
def noetherEulerValue_claim14675 : Prop :=
  ((13 : ℚ) + 11) / 12 = 2 ∧
    (12 : ℤ) ∣ (13 : ℤ) + 11

end MathlibPlus.Open.ResearchFormalization.NoetherClaim14675
