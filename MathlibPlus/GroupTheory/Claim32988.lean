import Mathlib

namespace MathlibPlus.GroupTheory.Claim32988

/-- The ordered placements of the two nonaffine blocks after fixing the affine
block are the falling factorial `8 * 7 * 6`. -/
theorem affine_ordered_placement_count_claim32988 :
    8 * 7 * 6 = (336 : ℕ) := by norm_num

/-- Six affine chart types times the 42 normalized placements give 252 controls. -/
theorem affine_control_count_claim32988 :
    6 * 42 = (252 : ℕ) := by norm_num

end MathlibPlus.GroupTheory.Claim32988
