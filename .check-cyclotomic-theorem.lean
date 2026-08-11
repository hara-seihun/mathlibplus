import Mathlib

namespace Test

/-- On the unit circle, the trace map is the real coordinate `2 Re z`. -/
theorem circleTrace_eq_two_re_13204 (z : Circle) :
    ((z : ℂ) + (z : ℂ)⁻¹).re = 2 * (z : ℂ).re := by
  have hz : (z : ℂ)⁻¹ = Complex.conj (z : ℂ) := by
    rw [← Circle.coe_inv_eq_conj]
    rfl
  rw [hz]
  simp [Complex.add_re]

end Test
