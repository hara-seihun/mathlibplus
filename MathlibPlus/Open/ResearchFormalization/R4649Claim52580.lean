import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4649

/-- Claim 52580: the exact self-dual parameter point and its right-hand
final-ray inequalities for Q-0136. -/
def claim52580_exactTargetSelfDualParameterPoint : Prop :=
  let L : ℝ := 1529 / 10000
  let T : ℝ := 44658961 / 312500000
  let Y : ℝ := 1767 / 12500
  let K : ℕ := 690988
  let N : ℕ := 2 * K
  let X : ℝ := 6000000185827
  let x : ℝ := 4 * Real.pi * (2 * (K : ℝ) ^ 2 - T / 16)
  N = 2 * K ∧
    T + Y ^ 2 / 2 = L ∧
      Y ^ 2 < 1 - 2 * T ∧
        x > X + Real.sqrt (1 - Y ^ 2)

end MathlibPlus.Open.ResearchFormalization.R4649
