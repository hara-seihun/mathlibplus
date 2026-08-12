import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open Polynomial

namespace MathlibPlus.LinearAlgebra.Claim11076

noncomputable section

/-- In the standard order `0,1,2,3,4`, the permutation matrix for
`k ↦ 2 k` modulo five has the stated characteristic polynomial. -/
theorem multiplicationByTwo_charpoly_claim11076 :
    let M : Matrix (Fin 5) (Fin 5) ℤ :=
      !![1, 0, 0, 0, 0;
          0, 0, 0, 1, 0;
          0, 1, 0, 0, 0;
          0, 0, 0, 0, 1;
          0, 0, 1, 0, 0]
    M.charpoly = (X - 1) ^ 2 * (X + 1) * (X ^ 2 + 1) := by
  dsimp
  classical
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.diagonal]
  ring

end

end MathlibPlus.LinearAlgebra.Claim11076
