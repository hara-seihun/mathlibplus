import Mathlib

namespace MathlibPlus.Open

/-- Exact benchmark-rate cost for all cutoffs in admitted claim 40848. -/
def exactSameRatePerCutoffCost : Prop :=
  let benchmark : ℝ := 42.64668679796159
  let cutoffs : ℝ := 3999309011
  let seconds := benchmark * cutoffs
  let hours := seconds / 3600
  let gpuYears := hours / (365 * 24)
  seconds = 170557278800.38252331888749 ∧
    47377021.888995145 < hours ∧
    hours < 47377021.888995146 ∧
    47377021 < hours ∧ hours ≤ 47377022 ∧
    5408 < gpuYears ∧ gpuYears < 5409

/-- Exact benchmark-rate cost for the thirteen blocks in admitted claim 40849. -/
def exactSameRatePerBlockCost : Prop :=
  let benchmark : ℝ := 42.64668679796159
  let blocks : ℝ := 13
  let seconds := benchmark * blocks
  let hours := seconds / 3600
  let minutes := seconds / 60
  seconds = 554.40692837350067 ∧
    0.15400192454819463 < hours ∧
    hours < 0.15400192454819464 ∧
    9.240115472891677 < minutes ∧
    minutes < 9.240115472891678 ∧
    9 < minutes ∧ minutes < 10

/-- Offered-capacity ratios relative to the per-cutoff price in admitted claim 40851. -/
def offeredCapacityShortfalls : Prop :=
  let benchmark : ℝ := 42.64668679796159
  let cutoffs : ℝ := 3999309011
  let price : ℝ := benchmark * cutoffs / 3600
  let sevenDayEightCard : ℝ := 8 * 7 * 24
  let sevenDaySixteenCard : ℝ := 16 * 7 * 24
  let sevenDaySixtyFourCard : ℝ := 64 * 7 * 24
  let thirtyDayEightCard : ℝ := 8 * 30 * 24
  sevenDayEightCard = 1344 ∧
    sevenDaySixteenCard = 2688 ∧
    sevenDaySixtyFourCard = 10752 ∧
    thirtyDayEightCard = 5760 ∧
    35250 < price / sevenDayEightCard ∧
    price / sevenDayEightCard < 35251 ∧
    17625 < price / sevenDaySixteenCard ∧
    price / sevenDaySixteenCard < 17626 ∧
    4406 < price / sevenDaySixtyFourCard ∧
    price / sevenDaySixtyFourCard < 4407 ∧
    8225 < price / thirtyDayEightCard ∧
    price / thirtyDayEightCard < 8226

end MathlibPlus.Open
