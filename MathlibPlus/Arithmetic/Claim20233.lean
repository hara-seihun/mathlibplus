import Mathlib.Tactic

namespace MathlibPlus.Arithmetic.Claim20233

/-! Exact rational arithmetic extracted from admitted claim 20233.

The decimal data in the source are treated as exact rational literals.  This
formalization records the stated transfer margin, not the analytic certificate
that produced the three constants.
-/

/-- The transfer cost is below the sparse threshold, which is below the
weakest certified endpoint, and the threshold slack is the stated positive
margin. -/
theorem sparseTransferMargin :
    let transferCost : ℚ := 0.0010985341346401207
    let sparseThreshold : ℚ := 0.0013
    let weakestEndpoint : ℚ := 0.0013129967228903067
    let transferMargin : ℚ := 0.0002014658653598793
    transferCost < sparseThreshold ∧
      sparseThreshold < weakestEndpoint ∧
      sparseThreshold - transferCost = transferMargin ∧
      0 < transferMargin := by
  norm_num

end MathlibPlus.Arithmetic.Claim20233
