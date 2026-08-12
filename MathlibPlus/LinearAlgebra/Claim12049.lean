import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

namespace MathlibPlus.LinearAlgebra

/--
Claim 12049 (packet `O-0231`): the explicit rank-two shift-one matrix from
the packet has deleted-row cofactors `(1/32, 9/64, 1/16)`, and its first
endpoint comparison is negative while the second is positive.
-/
theorem claim12049_deleted_row_cofactors :
    let A : Matrix (Fin 3) (Fin 2) ℚ :=
      !![1 / 4, 0;
         9 / 16, 1 / 4;
         73 / 64, 9 / 16]
    let Δ : Fin 3 → ℚ := fun i => Matrix.det (A.submatrix i.succAbove id)
    Δ 0 = 1 / 32 ∧ Δ 1 = 9 / 64 ∧ Δ 2 = 1 / 16 ∧
      Δ 0 - (1 / 4 : ℚ) * Δ 1 = -1 / 256 ∧
      Δ 1 - (1 / 4 : ℚ) * Δ 2 = 1 / 8 ∧
      Δ 0 - (1 / 4 : ℚ) * Δ 1 < 0 ∧
      0 < Δ 1 - (1 / 4 : ℚ) * Δ 2 := by
  dsimp
  simp [Matrix.det_fin_two, Fin.succAbove]
  norm_num

end MathlibPlus.LinearAlgebra
