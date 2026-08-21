-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.NumberTheory.Claim11579

/-- Exact finite Frobenius data from claim 11579. The matrix is the displayed
Frobenius matrix; the cohomological/abelianization interpretation is not
silently reconstructed because its carrier is not specified in the packet. -/
theorem ellipticFrobeniusFiniteCore_claim11579 :
    let F : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, -3]
    let P : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) := !![0, -5; 1, -3]
    Matrix.det ((1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) -
        (Polynomial.X : Polynomial ℤ) • P) =
        (1 : Polynomial ℤ) + 3 * Polynomial.X + 5 * Polynomial.X ^ 2 ∧
      ((5 : ℤ) ^ 1 + 1 - Matrix.trace (F ^ 1) = 9) ∧
      ((5 : ℤ) ^ 2 + 1 - Matrix.trace (F ^ 2) = 27) ∧
      ((5 : ℤ) ^ 3 + 1 - Matrix.trace (F ^ 3) = 108) ∧
      ((5 : ℤ) ^ 4 + 1 - Matrix.trace (F ^ 4) = 675) ∧
      ((5 : ℤ) ^ 5 + 1 - Matrix.trace (F ^ 5) = 3069) ∧
      ((5 : ℤ) ^ 6 + 1 - Matrix.trace (F ^ 6) = 15552) := by
  dsimp
  constructor
  · norm_num [Matrix.det_fin_two, Matrix.trace, Matrix.mul_apply]
    ring
  · native_decide

end MathlibPlus.NumberTheory.Claim11579
