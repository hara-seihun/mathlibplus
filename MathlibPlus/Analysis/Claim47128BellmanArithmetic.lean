import Mathlib

namespace MathlibPlus.Analysis.Claim47128

/--
The exact rational arithmetic in the claim's displayed transcript.  The
source-specific conditional-variance and potential definitions are not
reconstructed; they are represented by the four explicitly displayed rational
quantities and their exact-value hypotheses.
-/
theorem potentialSelectionAndDefectArithmetic_claim47128
    (variance phi deltaX deltaY : ℚ)
    (hvariance : variance = 1451 / 2916)
    (hphi : phi = 421 / 486)
    (hdeltaX : deltaX = 289 / 729)
    (hdeltaY : deltaY = 685 / 1458) :
    variance = 1451 / 2916 ∧
      phi = 421 / 486 ∧
      deltaX < deltaY ∧
      variance - deltaY = 1 / 36 ∧
      0 < (1 / 36 : ℚ) := by
  subst variance
  subst phi
  subst deltaX
  subst deltaY
  norm_num

end MathlibPlus.Analysis.Claim47128
