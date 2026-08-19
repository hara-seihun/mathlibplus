import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim44294

/-- The exact endpoint-minus-transfer reserve in the C-0130 transfer audit. -/
def exactTransferReserve_claim44294 : Prop :=
  let endpoint : ℚ := (114 : ℚ) / 100000
  let transferCost : ℚ :=
    (113438368318475277316736553698 : ℚ) / (10 : ℚ) ^ 32
  let reserve : ℚ :=
    (561631681524722683263446302 : ℚ) / (10 : ℚ) ^ 32
  endpoint - transferCost = reserve ∧ 0 < reserve

end MathlibPlus.Open.ResearchFormalization.Claim44294
