import Mathlib

namespace MathlibPlus.Analysis.Claim49765

/-- Exact rational certificate for the retained support-three law: the listed
weights are positive and normalized, and its direct-area margin is the exact
negative rational displayed in the packet.  The scan/deduplication carrier is
left explicit for fidelity review rather than replaced by an invented model. -/
theorem exactRetainedRatioCertificate_claim49765 :
    (0 : ℚ) < 1 / 14 ∧
    (0 : ℚ) < 6 / 7 ∧
    (1 / 14 : ℚ) + 6 / 7 + 1 / 14 = 1 ∧
    (320651 : ℚ) / 123462 < 3 ∧
    (320651 : ℚ) / 123462 - 3 = -(49735 : ℚ) / 123462 := by
  norm_num

end MathlibPlus.Analysis.Claim49765
