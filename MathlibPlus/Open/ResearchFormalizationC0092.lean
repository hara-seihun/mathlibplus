import Mathlib

namespace MathlibPlus.Open

/-- Claim 1414: the directed rational enclosure for the minor-arc constant. -/
def research_claim_1414 : Prop :=
  let c1 : ℝ :=
    (1 / 7) * (3 / 2 - Real.log 5 / Real.log 3) *
      (Real.log 2 / Real.log 10)
  let lower : ℝ := 1506288700915 / 10 ^ 15
  let upper : ℝ := 1506288700916 / 10 ^ 15
  c1 - lower > (273 / 100) * (10 : ℝ)⁻¹ ^ 16 ∧
    lower < c1 ∧ upper > c1

end MathlibPlus.Open
