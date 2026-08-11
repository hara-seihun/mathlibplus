import Mathlib

namespace MathlibPlus.Analysis.Claim45688

/-- The exact radical arithmetic displayed for the Bellman-defect witness.
The finite query carrier and the packet's Bellman-defect semantics are not
silently invented here; those are fidelity-review boundaries. -/
theorem exactMinimumBellmanDefectArithmetic_claim45688 :
    (13 + 16 - (19 + 6 * Real.sqrt 2 : ℝ)) / 121 =
      (10 - 6 * Real.sqrt 2) / 121 ∧
    0 < (10 - 6 * Real.sqrt 2) / 121 := by
  constructor
  · ring
  · have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      have h : (0 : ℝ) ≤ 2 := by norm_num
      simpa using Real.sq_sqrt h
    nlinarith

end MathlibPlus.Analysis.Claim45688
