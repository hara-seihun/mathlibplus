import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim1488

/-- The displayed right-endpoint improvement is the exact positive decimal
increment. -/
def exactRightEndpointImprovement : Prop :=
  (727.951336108 : ℚ) - 727.95133608031 = (2769 : ℚ) / 10 ^ 11 ∧
    0 < (727.951336108 : ℚ) - 727.95133608031

end MathlibPlus.Open.ResearchFormalization.Claim1488
