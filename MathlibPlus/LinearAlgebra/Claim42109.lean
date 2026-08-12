import MathlibPlus.Basic

open Polynomial
namespace MathlibPlus.LinearAlgebra.Claim42109

/-!
The matrix and target polynomial are fully displayed in claim 42109, so the
finite characteristic-polynomial calculation can be checked directly.  No
Lehmer or Salem interpretation is added beyond the stated matrix certificate.
-/

set_option maxHeartbeats 1000000 in
/-- The displayed integer matrix is symmetric. -/
theorem explicit_matrix_is_symmetric :
    let A : Matrix (Fin 5) (Fin 5) ℤ :=
      !![0, 1, 0, 0, 0;
         1, 0, 1, 0, 0;
         0, 1, 0, 1, 1;
         0, 0, 1, 0, 1;
         0, 0, 1, 1, -1]
    A = A.transpose := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1000000 in
/-- The characteristic polynomial of the displayed matrix is `Q_L`. -/
theorem charpoly_explicit_symmetric_matrix :
    let A : Matrix (Fin 5) (Fin 5) ℤ :=
      !![0, 1, 0, 0, 0;
         1, 0, 1, 0, 0;
         0, 1, 0, 1, 1;
         0, 0, 1, 0, 1;
         0, 0, 1, 1, -1]
    Matrix.charpoly A =
      X ^ 5 + X ^ 4 - 5 * X ^ 3 - 5 * X ^ 2 + 4 * X + 3 := by
  dsimp
  classical
  simp (discharger := decide) [Matrix.charpoly, Matrix.det_succ_column_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

end MathlibPlus.LinearAlgebra.Claim42109
