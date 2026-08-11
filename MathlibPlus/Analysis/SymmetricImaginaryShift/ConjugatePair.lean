import Mathlib

/-!
# Modulus-difference identities for symmetric imaginary shifts
-/

namespace MathlibPlus.Analysis.SymmetricImaginaryShift

/-- Exact modulus-product difference for a conjugate pair `u ± iv` under
symmetric imaginary shifts. -/
theorem conjugatePair_modulusDifference
    (u v x y a : ℝ) :
    let D : ℝ → ℝ := fun Y =>
      ((x - u) ^ 2 + (Y - v) ^ 2) * ((x - u) ^ 2 + (Y + v) ^ 2)
    D (y + a) - D (y - a) =
      8 * a * y * ((x - u) ^ 2 + y ^ 2 + a ^ 2 - v ^ 2) := by
  dsimp
  ring

end MathlibPlus.Analysis.SymmetricImaginaryShift
