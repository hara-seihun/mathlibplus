import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0266

/-- Claim 19322.  `Delta2` is the named scalar defect carrier; no formula
from an unstated construction is substituted for it. -/
def claim19322_everyInteriorAgeSmallAmplitudeNegativeDefect
    (Delta2 : ℝ → ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y ^ 2 → y ^ 2 < 8 →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : ℝ, 0 < q → q < ε → Delta2 q y < 0

end MathlibPlus.Open.Analysis.ResearchFormalizationR0266
