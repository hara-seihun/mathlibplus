import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 14680: for real `r`, `a`, `x`, and `y`, the squared-modulus
 difference of the two imaginary shifts of `z = x + iy` is `4ay`. -/
theorem complexModulusDifference_claim14680 (a r x y : ℝ) :
    let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
    ‖z + (a : ℂ) * Complex.I - (r : ℂ)‖ ^ 2 -
        ‖z - (a : ℂ) * Complex.I - (r : ℂ)‖ ^ 2 = 4 * a * y := by
  dsimp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

end MathlibPlus.Analysis
