import Mathlib.Data.Real.Basic

namespace MathlibPlus.Analysis.SlopeBounds

/-- Claim 15665: a strict slope bound remains strict after multiplication by a
positive order parameter. -/
theorem slopeBoundsTransfer (d U x : ℝ) (hdu : d < U) (hx : 0 < x) :
    d * x < U * x :=
  mul_lt_mul_of_pos_right hdu hx

end MathlibPlus.Analysis.SlopeBounds
