import MathlibPlus.Basic

namespace MathlibPlus.Open.Analysis

/--
Claim 58212: the pinned first-band interval receipt.  `center` and `radius`
are the exact rational values printed by the evaluator; the evaluator and
its `(T,Y)` carrier remain outside this registry node.
-/
def directedArbIntervalClaim58212
    (cutoffLower cutoffUpper : ℕ) (center radius : ℚ) : Prop :=
  cutoffLower = 690988 ∧
    cutoffUpper = 692000 ∧
    center =
      -(30199604517434826648849474203734533332615035617134 : ℚ) /
        (10 : ℚ) ^ 49 ∧
    radius = (186 : ℚ) / (10 : ℚ) ^ 52 ∧
    center + radius < 0 ∧
    center + radius < (57 : ℚ) / 50000

end MathlibPlus.Open.Analysis

namespace MathlibPlus.Analysis

/-- The displayed rational interval upper endpoint is strictly below both thresholds. -/
theorem directedArbIntervalUpperEndpoint_claim58212 :
    let center : ℚ :=
      -(30199604517434826648849474203734533332615035617134 : ℚ) /
        (10 : ℚ) ^ 49
    let radius : ℚ := (186 : ℚ) / (10 : ℚ) ^ 52
    center + radius < 0 ∧ center + radius < (57 : ℚ) / 50000 := by
  norm_num

end MathlibPlus.Analysis
