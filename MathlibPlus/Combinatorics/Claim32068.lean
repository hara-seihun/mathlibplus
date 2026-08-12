import Mathlib

namespace MathlibPlus.Combinatorics.Claim32068

/-- Cumulative block sizes for a ratio schedule, including the initial block. -/
def cumulativeBlockSizes (schedule : List ℕ) : List ℕ :=
  List.scanl (fun accumulated degree => accumulated * degree) 1 schedule

/-- The three exceptional schedules and their exact omission of block size three.
The normal-chain and Hall-join interpretations remain source-specific. -/
def exceptionalScheduleArithmetic : Prop :=
  cumulativeBlockSizes [2, 3, 2, 2] = [1, 2, 6, 12, 24] ∧
    cumulativeBlockSizes [2, 4, 3] = [1, 2, 8, 24] ∧
    cumulativeBlockSizes [4, 3, 2] = [1, 4, 12, 24] ∧
    3 ∉ cumulativeBlockSizes [2, 3, 2, 2] ∧
    3 ∉ cumulativeBlockSizes [2, 4, 3] ∧
    3 ∉ cumulativeBlockSizes [4, 3, 2]

theorem exceptionalScheduleArithmetic_proved : exceptionalScheduleArithmetic := by
  norm_num [exceptionalScheduleArithmetic, cumulativeBlockSizes]

end MathlibPlus.Combinatorics.Claim32068
