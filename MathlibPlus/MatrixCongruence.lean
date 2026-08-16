import Mathlib

/-!
# Determinants under matrix congruence

Kernel-checked formalization of Record 18 from source record `C-0023`.
-/

namespace MathlibPlus.MatrixCongruence

/-- Congruence by a square real matrix multiplies the determinant by the square of
the congruence matrix's determinant. In particular, an invertible rational
preconditioner cannot reverse determinant sign after scalar extension to `ℝ`. -/
theorem determinant_congruence {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.det (P * M * P.transpose) = Matrix.det P ^ 2 * Matrix.det M := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end MathlibPlus.MatrixCongruence
