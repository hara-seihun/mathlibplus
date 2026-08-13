import Mathlib

namespace MathlibPlus.Algebra.Claim13085

/-- The exact negative polynomial gap in claim 13085.  The source's
`Delta_0` and `Delta_1` carriers are not defined in the claim record; this
kernel-checked declaration retains the displayed scalar gap and its strict sign. -/
theorem negativeEndpointGap_core_claim13085 (t : ℝ) (ht : 0 < t) :
    -(t ^ 5 / 8192) *
        (t ^ 7 + 2 * t ^ 6 + 16 * t ^ 5 + 16 * t ^ 4 +
          128 * t ^ 3 + 256 * t ^ 2 + 2048) < 0 := by
  have hpoly : 0 <
      t ^ 7 + 2 * t ^ 6 + 16 * t ^ 5 + 16 * t ^ 4 +
        128 * t ^ 3 + 256 * t ^ 2 + 2048 := by
    positivity
  have hscale : 0 < t ^ 5 / 8192 := by positivity
  rw [neg_mul]
  exact neg_lt_zero.mpr (mul_pos hscale hpoly)

end MathlibPlus.Algebra.Claim13085
