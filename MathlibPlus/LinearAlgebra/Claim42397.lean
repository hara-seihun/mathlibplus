import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim42397

/-- A defect rank at least `2 * p + 3` lies strictly above the case range
bounded by `2 * p + 2`. -/
theorem defectRank_exceeds_caseRange
    (p r defectRank : ℕ)
    (hr : r ≤ 2 * p + 2)
    (hd : 2 * p + 3 ≤ defectRank) :
    r < defectRank := by
  omega

end MathlibPlus.LinearAlgebra.Claim42397
