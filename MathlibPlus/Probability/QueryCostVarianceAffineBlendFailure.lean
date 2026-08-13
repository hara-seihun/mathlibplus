import MathlibPlus.Open.Probability.QueryCostVarianceAffineBlendFailure

namespace MathlibPlus.Probability

open MathlibPlus.Open.Probability

theorem queryCostVarianceAffineBlendFailure_proof :
    queryCostVarianceAffineBlendFailure := by
  dsimp [queryCostVarianceAffineBlendFailure]
  intro α
  by_cases hlt : α < 1
  · right
    left
    constructor
    · ring
    · nlinarith
  · by_cases heq : α = 1
    · right
      right
      subst α
      norm_num
    · left
      have hge : 1 ≤ α := le_of_not_gt hlt
      have hgt : 1 < α := lt_of_le_of_ne hge (Ne.symm heq)
      nlinarith

end MathlibPlus.Probability
