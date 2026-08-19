import Mathlib

namespace MathlibPlus.Algebra.Claim4166

/-- The real-part reconstruction identity in claim 4166. -/
theorem realPartReconstruction (d beta kappa : ℝ) (hd : 0 < d)
    (hkappa : kappa = (2 * beta - 1) * d) :
    beta = (1 / 2 : ℝ) * (1 + kappa / d) := by
  field_simp [ne_of_gt hd]
  linarith

end MathlibPlus.Algebra.Claim4166
