import Mathlib

namespace MathlibPlus.Analysis

/--
On the complex unit circle, the trace map `z + z⁻¹` has real value `2 Re z`.
This is the coordinate used in the measure node for claim 13204.
-/
theorem circleTrace_eq_two_re_13204 (z : Circle) :
    ((z : ℂ) + (z : ℂ)⁻¹).re = 2 * (z : ℂ).re := by
  have hz : (z : ℂ)⁻¹ = (starRingEnd ℂ) (z : ℂ) := by
    rw [← Circle.coe_inv_eq_conj]
    rfl
  rw [hz]
  simp [Complex.add_re]
  ring

end MathlibPlus.Analysis
