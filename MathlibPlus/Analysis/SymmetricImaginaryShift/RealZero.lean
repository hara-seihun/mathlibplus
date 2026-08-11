import Mathlib

/-!
# Modulus-difference identities for symmetric imaginary shifts
-/

namespace MathlibPlus.Analysis.SymmetricImaginaryShift

/-- Exact squared-modulus difference for a real zero under symmetric
imaginary shifts. -/
theorem realZero_modulusDifference
    (r x y a : ℝ) :
    Complex.normSq
          ((x : ℂ) + Complex.I * (y + a : ℝ) - (r : ℂ)) -
        Complex.normSq
          ((x : ℂ) + Complex.I * (y - a : ℝ) - (r : ℂ)) =
      4 * a * y := by
  simp [Complex.normSq_apply]
  ring

end MathlibPlus.Analysis.SymmetricImaginaryShift
