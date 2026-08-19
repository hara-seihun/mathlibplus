import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.NoetherClaim14672

/-- Claim 14672: the displayed Noether quotient for `(c₁², c₂) = (12, 12)`
is `2`, and the corresponding integer sum is divisible by `12`. -/
def noetherEulerValue_claim14672 : Prop :=
  ((12 : ℚ) + 12) / 12 = 2 ∧
    (12 : ℤ) ∣ (12 : ℤ) + 12

end MathlibPlus.Open.ResearchFormalization.NoetherClaim14672
