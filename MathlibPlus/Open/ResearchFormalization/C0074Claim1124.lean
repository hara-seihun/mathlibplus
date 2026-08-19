import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0074Claim1124

/-- Claim 1124: the exact decimal amplitude difference and the positive
reciprocal-amplitude difference. -/
def claim1124 : Prop :=
  (51.34 : ℝ) - 51.331 = 9 / 1000 ∧
    (1 / 51.331 : ℝ) - 1 / 51.34 = 450 / 131766677 ∧
    (0 : ℝ) < 450 / 131766677

end MathlibPlus.Open.ResearchFormalization.C0074Claim1124
